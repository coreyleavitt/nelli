# RFC-0016 native-parity hardening — handoff

- **Stage:** Wave 1 shipped as **0.9.2** (2026-11-08): signed tag `v0.9.2`
  at `bc06d09f`, published `ghcr.io/coreyleavitt/nelli@sha256:925d0deb...`
  (content `dag-sha256:dded114f...`). Wave 2 in progress.
- **Resume:** `/loop` grind over Wave 2. Landed 2026-11-08: shm leak count
  `785fb31a`, K8a nightly batching `b1f17b39` (10 batches of 25 under a 12 GB
  guard; run 42497426347 green at 250 programs), INT-47 `846d18e9..4f682783`,
  k8a_sink under Git Bash `2a91b74a`, CI-B `06c2cb95` (nightly cpp/z3-4.13.4/
  msvc legs; ceiling ratchet one-sided at 60 s x 2.5 = 150 s, stale entries
  warn only; msvc known-red list empty; verification 42519745480 green),
  K1a-ci (post-shard universe join on all five rows, row-scoped allowlist
  entries; planted RED 42532198619, green 42537270847 / 42537270688 /
  42537276403), W2-z (Wave 2 integration, below). Wave 2 is complete; the
  eos calibration sweep was dropped because the full CI joins on all five
  rows calibrated the allowlists. Now Wave 3, one branch per slice, landed
  in order after its symex-linux and symex-mingw runs are green.
- **W2-z (2026-11-09):** integration sha `3fbb1676`. symex-nightly
  42543319693 (CI-B, all legs, universe joins green), k8a-differential
  42543321720, symex-linux 42543282587 (CI-A3 watchdog: K8a heartbeat 0 days,
  no open intake issue), symex-mingw 42543282339, fuzzer-mingw 42543282630:
  all green. fuzzer-msvc 42543282381 hit its 90-minute job timeout with 43 of
  45 walker files run (also on `06c2cb95`); the walker tests now run as their
  own `walker-msvc` job (run 42551700369: fuzzer-msvc 33 min, walker-msvc 39
  min, 45 files). The universe join now prints and checks a record census
  (fails on no SUT, or a full join with no exact verdict). Census at
  `407bd354`: linux-c 138 cells, 387 records over 72 files, 94 SUTs,
  exact 118 / declined 237 / raised 11 / crashed 9 / skipped 12 (symex-linux
  42557135225); mingw 384 records over 71 files, 94 SUTs, exact 118 /
  declined 235 / raised 11 / crashed 9 / skipped 11 (symex-mingw 42557135246).
  Every leg's record directory is nonempty. Open intake issues older than
  seven days: none.
- **Research:** `docs/rfc/0016-research/` (six lens reports, the merged list
  W-01..W-69, the magic table, the test classification). Snapshot 83c1d304,
  walker 272.
- **Open forks:** none.
- **Wave 1 progress (2026-11-07, `/loop` grind):** landed on `main` in order:
  INF-05 `977ca243`, K9a `595a2a8b`, W1-c3 `03fb59fc`, W1-a `c0e8bd44`
  (walker 273), W1-c1a `d4efde91`, W1-c2 `6d40f03c` (274), W1-p `7f45bc8e`,
  W1-c1b `24ab03ca`, W1-b `2b5a1f8e` (275), W1-g `05dbb256` (276), W1-e
  `86536fa9` (277), W1-f `3451144a` (278), CI-A1 `39cca9e5` (Wave 2,
  provisioning), W1-d1a `e044a290` (279), W1-d1b `682de5a4` (280), W1-d1c
  `b7296b78` (test only), CI-A2 `9540ecb3` (`sweep.sh --host`/`--derive`),
  W1-d3 `a22d7f5c` (281, codec v4), W1-d2 `0aa6b3bb` (282, 14 pin files
  rewritten, 8 `_checksoff` siblings), W1-d2c `0325b50f` (283, `push
  overflowChecks: on` in a checks-off build is checked), W1-m `154c56a0`
  (284; fuzzer-msvc runs every `tsymex_0016_*` under vcc; the re-exec replay
  confirms a SUT naming its own routine global), let-audit fix `42add4ed`,
  W1-z first half `a3836f09` (deprecations, `docs/migration/0.9.2.md`, README
  decline catalogue, `scripts/check-readme-kinds.sh`), stale-test migration
  `63a1f4a6`, Windows crash classifier `a6b2523e`. ADM-1 held on
  `origin/rfc-0016-adm1` `04cd1ab7` until after the 0.9.2 tag. K1-0 landed
  (`tests/k1lite.nim`, `scripts/k1lite.sh`). W1-z second half recorded
  2026-11-07: the three-way rows below, F-0001..F-0007 closed, RFC-0017 §7
  holds MOV-01's items, the spec corrections below applied to the RFC body.
  Remaining: file UPS-01 and UPS-03 (drafts are `docs/rfc/0016-research/UPS-01.md`
  and `UPS-03.md`; UPS-03 needs a reduction first), then the 0.9.2 gate.
- **0.9.2 release gate (2026-11-08):** whole-suite podman sweeps on eos at
  `bc06d09f` against the 0.9.1 baselines (`sweep-diff.sh`): c, cpp and
  z3-4.13.4 each unchanged=989 regressed=0 new-failing=0 new-ok=36; the one
  red (`s8by_remainder`, c and cpp) is in the baseline. Publish needed four
  reruns: GitHub release downloads (oras, cosign, Z3) returned 504
  intermittently for about an hour. The workflow_dispatch dry run cannot
  certify before the tag exists (milpa requires a `v<version>` tag at HEAD;
  a short sha is also read as a branch by checkout). FINDING, outside this
  repo: the tianguis `index.json` lists nelli at 0.3.5 only, although the
  publish dispatch answered HTTP 200 for 0.9.0, 0.9.1 and 0.9.2 (the OCI
  artifacts and tags are on GHCR); the index's last nelli-relevant change
  predates the rename (see the nelli-rename registry-aliasing item).
- **Wave 2 progress (2026-11-08):** on `main`: K5a, CI-A1/A2/A3, K9b, K2-s,
  K7a/b, K8-0 (earlier), K1a-cells `ed2982fd`, K9d-0 `2c4b48a5` (an
  infeasible concolic flip returns `cfoSolvedOptimistic`, never `cfoUnsat`),
  K8A-1 `ec719a37` (template `except T as e` macro-time crash), K1a-ids
  `f3a73be8` (work list as `docs/rfc-data/0016-worklist.toml`, rendered into
  §5 by `scripts/check-worklist.sh`), K8a-gen `4321230f`, K2-0 `79e6b18d`
  (SND-13, INT-22 soundness pins), INT-46 `4d343177` (the fork-safety guard
  counted joined threads still listed in `/proc/self/task`; now skips
  exiting/zombie/vanished tasks), K1a-last `b36dc4c4`, INT-45 test side
  `13578374` + `fuzzer-msvc` multi-glob/`nim_flags` `9ae34c9a`, K8a-job +
  K8a-sink + watchdog grace `8a13795f..e8630d44` with D1 in progress
  `42af2d2b` (first nightly dispatched; attempt 1 lost its runner, rerun),
  shm sweep fix `c39b770c` (below). CI-B (`rfc-0016-cib2`) green after the
  toolchain incident reruns; awaiting its agent's handoff.
  K1a-ci (`rfc-0016-k1aci`): post-shard universe joins on symex-linux, symex-mingw and symex-nightly; allowlist entries take an optional `rows=` scope (`heNilDerefMayBeCaught` is scoped to mingw, msvc, linux-cpp: setjmp is INT-12 on Windows and unbuildable on cpp); five stale `errorkind` entries deleted. Planted-RED nightly https://github.com/coreyleavitt/nelli/actions/runs/42532198619; green: linux https://github.com/coreyleavitt/nelli/actions/runs/42537270847, mingw https://github.com/coreyleavitt/nelli/actions/runs/42537270688, nightly (cpp, z3-4.13.4, msvc) https://github.com/coreyleavitt/nelli/actions/runs/42537276403.
- **Wave 3 progress (2026-11-08):** K2a (`rfc-0016-k2a`):
  `tests/tsymex_0016_k2a_census.nim`, registered in `nelli.nimble`, counts the
  `case n.kind` sites, `Survivors(`/`Degrade(` literals, bare `skip(` calls and
  platform arms in files without `skipCell`, and joins them to
  `tests/0016-allowlist/census.txt` (unlisted site and stale entry both fail;
  the K2-s script totals are cross-checked on Linux). K2a-fail (Wave 4) turns
  the bare `skip(` rows from listed into failing.
  K3a (`rfc-0016-k3a`, walker 290 to 291): `smt/typeaxes.nim` holds the
  type-class axis (`typeClassTable`, one row per `NimTypeKind` plus the named
  features, `admitTypeClass`; `typeCopiedByValue` reads it) and the type x
  memory-op axis (`typeOpTable`, `letCursor/<IR kind>`, `admitTypeOp`;
  `holdsSharedMemory` moved there and now fails closed: it looks through a
  variant, a multi-variant and a distinct, so `let c = gV` over a case object
  holding a seq arm declines like its plain-object twin, B-04). STY-04 is
  `never` (`typeclass:owned`, `typeclass:atomic`); STY-06 stays open with its
  K3a cells (`typeclass:float128`, `typeclass:float/sNaNPayload`). `fieldDefault/*`
  is K3b's; `cast/`, `not/`, `ptr/lt`, `set/char/*` are not memory operations and
  stay orphans for the construct and definedness axes.
  The named-feature rows (`tcFeature`) have no consumer yet: `classifyType`
  does not consult them. K2c, which owns `classifyType`, wires them.
  K4a-table (`rfc-0016-k4at`): the magic
  axis is `smt/magic_rows.nim`'s `magicAxis`, 216 rows keyed by `TMagic` name
  (from `0016-research/magic_table.md`) plus `nextafter` (STY-05, a `never`
  cell, `nrTheory`); `varParamMagics` is a subset with the same verdict, and
  the universe derives its `magic:` cells from `magicAxis`. The lib-wide guard
  (`tsymex_0016_k4a_table`) fails on a `magic:` pragma anywhere in `lib/` with
  no row. The `vsArm` site stays unconsumed: the per-site dispatch is
  K4a-dispatch's. All 217 `magic:` cells are allowlisted under K4a-dispatch
  (no pin writes a record for them yet; `skipCell` on `magic:DivU` is not a
  classifying verdict).
  K5b (`rfc-0016-k5b`): `buildprofile.nim` gains `BuildProvenance.stockNim`
  (two compile-time probes for backports 25858 and 26093, the only ones a
  `compiles` can reach; a toolchain with neither reads as stock), `bfNim`, and
  `buildCells` (refusal, hazard and cfg cells of the build axis, keyed like
  `mm=refc`). Refused by name: 32-bit, big-endian, arm64, macOS, `fwrapv` under
  vcc, an unpatched Nim, an unverified Z3 (`pinAdmission` over a synthetic
  build; `--cpu:i386` also as a real child build). The stock-Nim slice runs
  `tsymex_0016_k5b_stock.nim` under `NELLI_STOCK_NIM=<unmodified nim>` (no CI
  leg has one). Cfg suites `tsymex_0016_k5b_cfg_*` (mm arc, atomicArc,
  useMalloc, setjmp, release, nelliFwrapv) share `k5b_cfg_body.nim`; W-51 is
  those memory pins plus `tsymex_0016_k5b_pcre`. STY-01, STY-08, AUD-01 and
  W-52's `sizeof` are `never` cells (`pinNever`); refc's is `mm=refc`. The
  walker version is unchanged. Windows-leg claims (8.37 JIT cells, mingw
  setjmp skip, msvc fwrapv skip) are `rows=`-scoped allowlist entries that
  no Windows run has confirmed yet.
  K2b (`rfc-0016-k2b`, walker 291->292): every `float32` <-> `float64`
  conversion is exact. W1-e had already made int->float exact and kept the
  widening of a binary operand; K2b replaces the remaining `feFloatWidth`
  decline (explicit narrowing and widening, hidden argument/initialiser
  widening) with `toFloat32` / `toFloat64` `iekMathCall`s lowered to
  `fp.to_fp` RNE. Pins in `tests/tsymex_0016_w1e_floatwidth.nim` cover 0.1,
  both float32 ties (to even), overflow to infinity, the three conv cells.
  `feFloatWidth` is now unproduced: allowlisted in `errorkind.txt` for K9c /
  W-64. Float-to-int stays K10a-float. PRC-40 resolved. STY-06's float80 /
  sNaN `never` cell is not created here (needs the admission-table `never`
  machinery of K3a/K4c). K3a also takes the walker to 291: expect a conflict
  in `canonicalize.nim` and the CR2 pin.
  K10a-target (`rfc-0016-k10at`, walker 292 to 293):
  `stkUndefined` and `tUndefined(kinds = allUbKinds)` (`types.nim`), the
  `UndefinedFinding[T]` list `SymexResult.undefined`, and `FindingUndefined` /
  `SymexFinding.undefined` (`engine/types.nim`). The one producer is
  `haltUndefined` (`runtime.nim`): the undefined side is solved on the path
  plus its condition. Under `tUndefined` a listed kind is the hit (a clean
  `sxSat`, `witnessUndefined` set, so never `trusted()` and never run in the
  host); under any other target it is listed, once per (kind, site), at most
  `maxUndefinedFindings` (8) per run, clean paths only, and the halt message
  names `tUndefined()` as the next query. The path ends either way, so a
  `tUndefined` `sxUnsat` is trusted only where no undefined side was reachable.
  Consumers: `describeTarget`, `canonicalize(SymexTarget)` (`Tg<UD:...>`),
  `wireTarget`/`readTarget`, `replayInScope` and `replayReached` (false: replay
  never runs the witness), `assertCoveredBy` (never covered), `targetLit` and
  the `bindSym` splices, the `:notes` record (`:undef:<i>` entries, `undefn`),
  so a cache hit serves the cold run's list. `symexForAll` does not discover a
  `tUndefined` target. K10a-axis extends the producers: every new definedness
  row calls `haltUndefined` with its `UbKind` and gets the target, the list and
  the cache for free. Traps: `UbKind` is a range that omits 0, so a field of it
  needs a declared default (`= ubUnsignedDivZero`) or `setLen` warns; a doc
  comment after `discard` in a variant branch breaks indentation.
- **INT-45 `s8bz_overlap` root cause (2026-11-08):** a Nim 2.2.10 codegen
  defect, not nelli. `compiler/cbuilder.nim` `addFieldWithStructType` writes
  a packed case object's branch `#pragma pack(pop)` into the enclosing
  record's builder (`result`) instead of the union body (`obj`), so under
  vcc the pops land before the union and pack(1) leaks to every later struct
  in the module (`sizeof(VariantArm)` 65 in the test's C vs 72 in
  `types.nim`'s). Fixed upstream in devel (nim-lang/Nim#24461, `b7b1003e6a`),
  never backported to 2.2. Our toolchain series gained patch 0007 (toolchain
  `3a4c85f`, with a vcc pack-depth check that runs without MSVC); published
  `2.2.10-windows-x64`; `fuzzer-msvc` run 42489572022 passes `s8bz_overlap`
  under vcc. Upstream backport request drafted at
  `scratchpad/nim-upstream-vcc-pack.md`, not filed.
- **Toolchain incident (2026-11-08):** that toolchain push republished
  `2.2.10-linux-x64` from the Tumbleweed (rolling) image; its `bin/nim`
  needed GLIBC_2.44 and every Linux CI job failed at setup from about 12:54
  to 13:50Z. Rolled back by manifest PUT, then fixed at the root (toolchain
  `8b56a3d`, `855bf4f`, `abc9b14`): the glibc artifacts now build on
  ubuntu-22.04 runners with a pre-publish GLIBC floor guard (2.35), and
  macOS moved to `macos-15` (the `macos-14` arm64 configuration is no
  longer provisioned). New `linux-x64` `332425eb` verified on stock Ubuntu
  24.04. Lesson: record every tag digest before a toolchain push.
- **Shm sweep (2026-11-08):** the intermittent `tfuzzcmplogshm` red was a
  product bug: `db.nim`'s campaign-startup `sweepStaleShmSegments` unlinked
  every `/dev/shm/nelli_*` segment, including a live sibling campaign's (or
  a parallel test's), so its reader re-created an empty segment. The sweep
  now spares segments whose embedded owner pid is alive (`c39b770c`,
  RED in `tdbcleanupsweep`). Residual limit: pid namespaces that share
  `/dev/shm`. Decisions: keep `fuzzer-msvc`'s per-push vcc step; fix MSVC
  defects rather than allowlist them.
- **Gate lesson (2026-11-07):** slices landed on their own suites only, and
  the Windows legs' runs on `main` were cancelled by each next push, so the
  W1-d2/W1-d1b/W1-m/W1-d3 contract changes left 11 stale files (red on Linux
  and Windows) plus a let-audit red that no run surfaced until symex-mingw
  finished at `42add4ed`. Fixed by `42add4ed`, `63a1f4a6`, `a6b2523e`. From
  here a slice that changes a contract runs every test naming the changed
  surface (`command grep -l`) before landing, and the 0.9.2 gate is the
  whole-suite podman sweep on eos at the W1-z sha (CI host sweep is not yet
  a gate: the `symex-linux` job's 45-minute cap ran 246 of ~900 tests, and
  four fuzzer tests, `tfuzzcovdump`, `tfuzzcovreset`, `tfuzzworkerprocess`,
  `tfuzzworkerspawnfailshm`, fail on the ubuntu-24.04 host while green in the
  0.9.1 podman baseline; both are CI-A3's to fix).
- **CI-A3 (2026-11-08):** `symex-linux` now runs every registered test (1031)
  in sharded `sweep` jobs, joined by a `gate` job against
  `tests/0016-allowlist/linux-host-known-red.txt` (fails on a new red, a
  stale entry, or a test with no result), with a `watchdog` job
  (`scripts/rfc0016-watchdog.sh`). The four fuzzer reds were host environment,
  fixed in `scripts/dt-bounded.sh`'s host path: `tfuzzcovdump`/`tfuzzcovreset`
  shared `/tmp/ptcov_build_*` between parallel workers (now a private
  `TMPDIR` per test), and `tfuzzworkerprocess` R23 / `tfuzzworkerspawnfailshm`
  R53 tighten `RLIMIT_NOFILE` to the open-fd count plus one, which fails to
  starve `pipe()` when the runner leaks fds 142 and 145 into the test (now
  fds above 2 are closed). The one remaining host red is INT-43. An F row names
  its `rfc-0016-intake` issue as `#N` in its `source` cell; the watchdog reads
  that. The K8a heartbeat is the `k8a-heartbeat` artifact of a
  `.github/workflows/k8a-*.yaml` workflow; the check arms itself when such a
  workflow exists and is a loud "NOT ARMED" notice until then.
- **CI-B (2026-11-08):** `.github/workflows/symex-nightly.yaml` runs three legs on `schedule`
  (03:17 UTC) and `workflow_dispatch` (`ref`, `legs`, `tests_regex`, `intake`): `cpp` (Linux, Z3 5.1.0),
  `z3-4.13.4` (Linux, c, the glibc-2.35 archive, sha in the workflow) and `msvc` (`symex-msvc`: windows-2025,
  c with vcc, the 896 `tsymex_*` tests in 26 shards; run through `scripts/run-ci-suite.ps1 -Cc vcc`). Shards come from
  `scripts/derive-linux-shards.py` (env knobs for prefix, jobs, target). Each leg is gated by its own
  allowlist `tests/0016-allowlist/nightly-<leg>-known-red.txt` with the stale-entry rule. CI-C: every leg uploads
  `nightly-<leg>-merged` (merged log, `.times`, gate, ceiling, diff) and diffs with `sweep-diff.sh` against the newest
  main artifact (`scripts/ci-baseline.sh`), else the 0.9.1 release row (informational), else none (msvc, first run).
  CI-D: `sweep.sh` writes `<log>.times` and compiler warnings are captured (stdout and stderr; `dt-bounded.sh` no
  longer loses a child's stderr, with a self-test). `scripts/check-ceiling.sh` is a GATE (the `report` job) with
  per-leg offender lists `tests/0016-allowlist/ceiling-offenders-<leg>.txt` and a one-sided gate: measured run-to-run
  per-test ratios over runs 42487154319, 42494651488 and 42508458773 had p5 0.46 to 0.67, p95 1.54 to 1.87 and msvc
  tails past 3x, so no symmetric band held. An unlisted test fails only above 150 s (60 x 2.5); between 60 and 150 s
  it warns; a listed entry that ran under 60 s warns as a stale entry and never fails. Every warning is an intake
  finding (leg `ceiling-<leg>`) that feeds a periodic re-seed. Lists are seeded with the union of tests over 60 s in
  any of the three runs; leave-one-out (seed from two, test the third) gives 0 new offenders per leg per fold at 2.5
  (at 2.0 msvc gives one: `tsymex_0016_k8a1_template_except_as`, 12.3, 10.2 then 125.7 s; 2.1 would clear it by 0.3 s, so 2.5 for margin). `scripts/vm-alias-slice.sh` builds `tsymex_rfc0005_s8ab_letaudit`
  plus a rotating 12-test slice with `-d:nelliVmAliasAudit`. `scripts/rfc0016-intake.sh` files `rfc-0016-intake` issues
  keyed `leg:test` (more than 10 on a leg collapse to `leg:*`); only `schedule`, or a dispatch with `intake: live`,
  files; everything else prints `[dry-run]` lines. Defect rows: INT-44 (cpp unit pin), INT-45 (MSVC-only reds; the s8bz
  cause was toolchain patch 0007), INT-46 (tfuzzforkworker thread race) and INT-47 (four MSVC-only reds, fixed on main)
  are closed, and the msvc known-red list is empty. W-63 closed against the msvc leg.
  `fuzzer-msvc` still carries its W1-m `tsymex_0016_*` step (kept: the nightly msvc leg is not per-push).
- **Windows native facts:** a Nim probe's division fault on Windows prints
  `SIGFPE: Arithmetic error` and exits 1 (the CRT maps 0xC0000094); `low(int)
  mod -1`/`div -1` raise 0xC0000095, which the mingw CRT does not map, so
  without the probes' first-chance handler the process sat in WER until the
  20 s budget and was killed with code 0. With the handler both trap, as on
  Linux.
- **0.9.1 baselines:** still running on eos (`~/nelli/bl091.sh`, logs
  `~/nelli/bl091-{c,cpp,z3-4.13.4}.log`); upload as `v0.9.1` release assets
  and list in `tests/0016-baselines.txt` when `~/nelli/bl091.all.done` exists.
- **Spec corrections found in implementation (applied to the RFC body 2026-11-07, W1-z):** W1-c2's RED
  expects `sxUnsat` for the label; the walker's established Defect rule (E6)
  gives `sxRaised` with `witnessUnsafe`, never `sxSat`, which is the
  intended property. SND-07's `ua3_diff` is not a native HIT (native never
  reaches `diff`; the decline is conservative, a precision row). W1-c2 sets
  `witnessUnsafe` on every crash claim, not only panics ones. W1-f: the
  field-default decline premise was wrong (native `var o: T` reads zero,
  `default(T)`/ctors/`new` apply defaults; the walker already agreed in every
  shape); W-20's compile stop was an empty `seq` default reaching the parser
  as a bare `[]`, fixed by lowering typed `seq` brackets as seq literals.
  W1-d1a: natively `low(int) mod -1` is SIGFPE on x86-64 (never the label);
  the halt is still right (C leaves it undefined). W1-d1a cost vs 0.9.1:
  identical Z3 check counts; units unchanged on guarded SUTs, ~3x on the one
  SUT whose undefined side is reachable on a sat path. W1-d1b: unsigned
  div/mod by zero SIGFPE natively (signed raises `DivByZeroDefect`); an
  opaque callee's unsigned division now forks no Defect and is not yet
  answered "undefined" (the opaque-scan "may be undefined" answer is §9.1
  item 3, K10b). ADM-1's spike changed the interface (feed into the RFC at
  W1-z): the decline kind is `Option[SymexErrorKind]` (PCRE's refusal is not
  a `SymexErrorKind`); a row is admitted per site set with an `elsewhere`
  kind; the key type parameter is dropped (string keys); rows are a `const`
  seq; the per-axis verbs live beside their payload types (import cycles).
  The `vsArm` site is declared but consumed only at K4a. W1-z first half:
  Nim 2.2 rejects `{.deprecated: "msg".}` on an object field, so `arithChecks`
  and `SymexResult.fromCache` carry the bare pragma and the path forward is in
  the doc comment and the migration note (the row's "path in the message"
  cannot hold for fields). A `--rangeChecks:off` build declines every routine
  `feCheckOption` (PRC-07/PRC-08, later waves).

## Findings ledger (§3.2), newest at the bottom

Severity against the 0.9.1 release is measured in "Three-way rows (W1-z)"
below (2026-11-07). F-0001..F-0007 are closed by their fix shas. Evidence V = coordinator re-ran walker and native on one
build; P = the lens did.

| F | date | class | vs release | source | shape | evidence | fix | state |
|---|---|---|---|---|---|---|---|---|
| F-0001 | 2026-11-06 | soundness | better | research lens A | `except T as e:` (W-01) | V | W1-a | closed `c0e8bd44` (2026-11-07) |
| F-0002 | 2026-11-06 | soundness | worse (precision) | research lens B | local `{.cursor.}` (W-02) | V | W1-b | closed `2b5a1f8e` (2026-11-07) |
| F-0003 | 2026-11-06 | soundness | better | research lens D | `--panics:on` Defect path (W-03) | V | W1-c2 | closed `6d40f03c` (2026-11-07) |
| F-0004 | 2026-11-06 | soundness | worse (precision) | research lens A | float32/float64 conversion (W-04) | P | W1-e | closed `86536fa9` (2026-11-07) |
| F-0005 | 2026-11-06 | soundness | better | research lens C | `low(int) mod -1`, literal divisor (W-05) | P | W1-d1a | closed `e044a290` (2026-11-07) |
| F-0006 | 2026-11-06 | soundness | better | research lens B | unsigned div/mod by zero (W-06) | P | W1-d1b | closed `682de5a4` (2026-11-07) |
| F-0007 | 2026-11-06 | soundness | same | research lens D | checks-off signed wrap (W-07) | P | W1-d2 | closed `0aa6b3bb` (2026-11-07) |

## Three-way rows (W1-z)

Recorded 2026-11-07. Probes: `tests/zz_threeway091*.nim` (not committed),
each run twice on c, once with the walker at the 0.9.1 tag and once at head
(`5e2728cf`), Nim 2.2.10 patched, Z3 5.1, and on one build the native
program (`symexCaptureBegin`/`symexCaptureEnd`). Variants: base, `_c1`, `_c2`,
`_fd`, `_fdseq`, `_off` (`--overflowChecks:off`), `_pan` (`--panics:on`).
Cell key is the K1-0 key where the row has one (`tests/k1lite.nim`), else `-`.
"vs release" is `same` (0.9.1 already behaved the same way), `better` (head is
closer to native) or `worse`. A row worse in soundness blocks the tag (the
RFC-0005 release rule); a precision loss the RFC itself specifies as a decline
does not. Native
`not probed` means the probe had no native run for the row; the native column
then gives what Nim guarantees and its source.

| row | cell key | 0.9.1 | head | native | vs release |
|---|---|---|---|---|---|
| W1-a `except ValueError as e` label (k=3) | `construct:except-as-label` | `sxUnsat` trusted | `sxSat` trusted | hit "h" | better |
| W1-a `as e`, `tRaisedExn("ValueError")` | `construct:except-as-raise` | `sxRaised` ValueError | `sxUnsat` trusted | caught, no raise | better |
| W1-b local `{.cursor.}` alias label | `pragma:local/cursor` | `sxSat` trusted | `sxUnknown`, `feLocalPragma` | hit "shared" | worse: precision only, a designed decline (W1-b); 0.9.1 agreed with native on this shape and the probe did not reproduce the false pair |
| W1-e `float64(float32(x)) == x` label | `construct:conv/float32<-float64` | `sxSat` trusted | `sxUnknown`, `feFloatWidth` | x=0.5 hit, x=0.1 no hit | worse: precision only, a designed decline (W1-e); the probe's label verdict was right in 0.9.1 and its witness was not checked |
| W1-g `x in 0 .. 10` (sat) | - | `sxUnknown`, `feUnsupportedOp` | `sxSat` trusted | hit at 7 | better |
| W1-g `x notin 0 .. 10` (sat) | - | `sxUnknown` | `sxSat` trusted | not probed (expected hit at 11) | better |
| W1-g `c in 'a' .. 'z'` (sat) | - | `sxUnknown` | `sxSat` trusted | not probed (expected hit at 'q') | better |
| W1-g enum `in eB .. eD` with `eE` (unsat) | - | `sxUnknown` | `sxUnsat` trusted | no hit | better |
| W1-g empty variable bounds (unsat) | - | `sxUnknown` | `sxUnsat` trusted | not probed (a..b with 5..3 holds nothing by definition) | better |
| W1-c2 `except Defect` label under `--panics:on` | `construct:panic-overflow-defect` | `sxSat` trusted | `sxRaised` OverflowDefect, `witnessUnsafe` | not probed (a panic is fatal and uncatchable, so no hit) | better |
| W1-c2 `finally` label under panics | `construct:panic-overflow-defect` | `sxSat` trusted | `sxRaised` OverflowDefect | not probed (as above) | better |
| W1-c2 escape, `tRaisedExn("OverflowDefect")` under panics | `construct:panic-overflow-defect` | `sxRaised` | `sxRaised` | not probed | same |
| W1-d1a `low(int) mod -1` label | `defined:mod/intMin/minusOne` | `sxUnsat` trusted | `sxUnknown`, `ubIntMinModMinusOne` | SIGFPE (never the label) | better: a trusted unreachable claim over a crash became a named decline |
| W1-d1a `int16` `low mod -1` (defined) | - | `sxSat` trusted | `sxSat` trusted | defined, hits | same |
| W1-d1a `x div -1` checked, `tRaisedExn("OverflowDefect")` | - | `sxRaised` OverflowDefect | `sxRaised` OverflowDefect | OverflowDefect | same |
| W1-d1a `--overflowChecks:off` `low div -1` | `defined:add/signed/checksOff` | `sxUnknown`, `feOverflowCheckOption` | `sxUnknown`, `ubSignedOverflow` | not probed | same |
| W1-d1b `10'u64 div k`, `r == 11` (unreachable) | `defined:div/unsigned/zero` | `sxRaised` DivByZeroDefect | `sxUnknown`, `ubUnsignedDivZero` | k=0 is SIGFPE, `r == 11` never | better |
| W1-d1b `r == 5` (sat) | `defined:div/unsigned/zero` | `sxSat` trusted | `sxSat` trusted (`ubUnsignedDivZero` noted) | hit at k=2 | same |
| W1-d1b unsigned div, `tRaisedExn("DivByZeroDefect")` | `defined:div/unsigned/zero` | `sxRaised` | `sxUnknown`, `ubUnsignedDivZero` | SIGFPE, not a Defect | better |
| W1-d1b `except DivByZeroDefect` label | `defined:div/unsigned/zero` | `sxSat` trusted | `sxUnknown`, `ubUnsignedDivZero` | SIGFPE, label never hit | better |
| W1-d1b signed `10 div k` raised | - | `sxRaised` DivByZeroDefect | `sxRaised` DivByZeroDefect | DivByZeroDefect | same |
| W1-d2 `{.push overflowChecks: off.}` `v + 1 > v` else-label | `defined:add/signed/checksOff` | `sxUnknown`, `feOverflowCheckOption` | `sxUnknown`, `feOverflowCheckOption` | no hit at `high(int)` (gcc folds the compare) | same |
| W1-d2 `--overflowChecks:off` add | `defined:add/signed/checksOff` | `sxUnknown`, `feOverflowCheckOption` | `sxUnknown`, `ubSignedOverflow` | no hit | same: 0.9.1 already declined at the source scan, so this probe reproduces no false verdict |
| W1-d2 `--overflowChecks:off` sub | `defined:add/signed/checksOff` | `sxUnknown`, `feOverflowCheckOption` | `sxUnknown`, `ubSignedOverflow` | not probed | same |
| W1-d2 `--overflowChecks:off` mul | `defined:add/signed/checksOff` | `sxUnknown`, `feOverflowCheckOption` | `sxUnknown`, `ubSignedOverflow` | not probed | same |
| W1-d2c `push overflowChecks: on` in a checks-off build, label | - | `sxRaised` OverflowDefect | `sxRaised` OverflowDefect | OverflowDefect | same |
| W1-d2c same, `tRaisedExn("OverflowDefect")` | - | `sxRaised` | `sxRaised` | OverflowDefect | same |
| W1-d3 `{.noinit.}` read, label | - | `sxSat` trusted, `feGlobalHavoc` | `sxSat` untrusted, `feGlobalHavoc` | not probed (stack-dependent by definition) | better: the claim is no longer trusted |
| W1-d3 `{.noinit.}` written before read | - | `sxSat` trusted | `sxSat` trusted | hit | same |
| W1-f `var o: O` with `x: int = 5` (unsat) | - | `sxUnsat` trusted | `sxUnsat` trusted | zero read, no hit | same |
| W1-f `default(O)` (sat) | - | `sxSat` trusted | `sxSat` trusted | hit | same |
| W1-f `seq[int] = @[]` field default | - | compile stop (index out of bounds in the parser) | `sxSat` | not probed | better |
| W1-f `case`/`elif`, statement form | - | compile stop (`unexpected case-arm kind nnkElifBranch`) | `sxSat` trusted | hit at 6 | better |
| W1-f `case`/`elif`, expression form | - | compile stop | `sxSat` trusted | hit at 6 | better |

Summary: 34 rows. better 17, same 15, worse 2. No row is worse in
soundness. The two `worse` rows, W1-b `{.cursor.}` and W1-e float width, are
precision losses by design: the spec makes each a named decline
(`feLocalPragma`, `feFloatWidth`), and on the probed label shape 0.9.1
happened to agree with native. Neither blocks 0.9.2: W1-b and W1-e's spec
rows name these exact shapes and verdicts (§11, "today a trusted false
pair"), and the decline is what makes the hidden-witness twins sound.
Recovering the precision is PRC-39 and PRC-40 (Wave 4, "the precision rows"). Not probed: the hidden-witness
shapes that made F-0002 and F-0004 false verdicts in 0.9.1 (the probes
asserted the label, not the witness values), and Windows.

## Round 1 ledger (2026-11-06)

Five lenses (liveness, depth, design, breadth, feasibility). Every point was
resolved by recommendation; none reached Corey.

| # | lens | finding | resolution |
|---|---|---|---|
| 1 | liveness | K1 "reporting first" is green-but-inert | ratchet allowlist failing from the first commit, planted RED per leg (§8.2) |
| 2 | liveness | no Linux or cpp CI leg runs the test task | CI-A/CI-B precede K1a (§11 Wave 2) |
| 3 | liveness | K8 host (sls2) offline, no `schedule:` workflow | K8a skeleton in Wave 2 on a scheduled Linux job; §4.2 corrected |
| 4 | liveness | Wave 1 W-03 needs a profile producer | minimal `buildProfile` const in W1-c, constructor-only grep pin (§8.3) |
| 5 | liveness | F-NNNN ledger never created | this file, F-0001..F-0007 |
| 6 | liveness | exact cells pinned outside public entry points | K1 refuses them (§10) |
| 7 | depth | UB is not sequenced: trusting a prefix-defined witness is unsound | whole-run definedness check on the winning path (§9.1 item 3); model continuation chosen over UBSan replay at verdict time, which needs a sanitizer build of the consumer |
| 8 | depth | UB on the default build too; `arithTrapConds` is x86-only | default build is a row of `admitDefinedness`; trap model retired (§9) |
| 9 | depth | W-13 noinit is not UB-as-halt | replay-side unconfirmable mark, MSan/valgrind pin (§9 "Not in K10") |
| 10 | depth | cell granularity ill-defined; K1 overclaims | cell = (dispatch site, arm key); single-site only; pairwise figure in §12 |
| 11 | depth | grep gates can be dodged | K2 census parses the AST; K7 by type (`Survivors`) |
| 12 | depth | `sxUndefined` breaks every exhaustive status case | no new status; `stkUndefined` target + `ubUndefinedBehaviour` halt (design lens's proposal) |
| 13 | depth | K5 should read effective C flags; compiler is a pin axis | §8.3 |
| 14 | design | hand-annotated TSV is a second source of truth | ledger generated from admission tables (§8.2) |
| 15 | design | K2-K6 are one mechanism | `smt/admission.nim`, `Admission[K]`, `feUnadmitted` (§8.1) |
| 16 | design | BuildProfile scattered | one const, three derivations (§8.3) |
| 17 | design | K7 grep acceptable | overruled by #11 |
| 18 | breadth | oracle not in the universe | §10: boundary values, witness-directed, sampled state, sanitized native rows, render round-trip, VM column |
| 19 | breadth | missing axes | call-site × callee shape, exceptions × memory (§8.2) |
| 20 | breadth | other NimNode parsers outside dsl_parser | K2 census covers all of `src/nelli` |
| 21 | breadth | MSVC/mingw have no UBSan; arm64 differs | declared Windows cells; arm64/macOS compile-only legs (§8.3, §9.1) |
| 22 | breadth | alternatives unweighed | §13 (post-transf AST, CBMC/KLEE recorded) |
| 23 | breadth | K8 across every build ≈100 h/day | one build row per night rotation (§11) |
| 24 | feasibility | seven parallel bumps | Wave 1 integrated as one bump (W1-z) |
| 25 | feasibility | W-05/06/07 are K10 (breaking) yet listed for 0.9.2 | 0.9.2 ships the fail-closed decline; K10 restores precision in 0.10.0 (§9 last paragraph) |
| 26 | feasibility | `staticRead` of ~850 tests too costly | pin-file checks at run time (§8.2) |
| 27 | feasibility | `holdsSharedMemory` not found | refuted: `dsl_parser.nim:16561` |
| 28 | feasibility | K4c/K6/K10b flip verdicts broadly | marked *round*, gated by a pinned sweep baseline (§11) |
| 29 | feasibility | `bindsViewWhole` is IR-level | stays separate from `mayWrite` (§8.1) |
| 30 | feasibility | `Admission[K]` designed against one consumer | ADM-1 spike moves `varParamMagics` and `verifiedLibs` onto it first |

**For round 2:** apply E-reconcile's corrections to §5.1-§5.8 (closures,
duplicates, stale evidence, reclassifications); check §8-§13 against the code
once more (the admission table list, the 20 degrade sites, the census reach);
stale CLAUDE.md lines (active RFC, "not green on a good day") are a
repo-hygiene edit outside this RFC.

## Round 2 ledger (2026-11-06)

Five Fable lenses on `ff843ccc`; a sonnet agent applied the breadth lens's
row-by-row §5 reconciliation. Every point resolved by recommendation; none
reached Corey.

| # | lens | finding | resolution |
|---|---|---|---|
| 1 | depth | shifts are masked by Nim's codegen (`ccgexprs.nim:665-667`), not UB | §9 corrected; shift decline dropped from W1-d; `shiftCountBV` is a defined row |
| 2 | depth | a UB halt taints runs whose UB side is infeasible | halt only if `pc ∧ cond` sat, decided once per path at exit (§9.1 item 2) |
| 3 | depth | whole-run check has no lattice home; replay could override it | `Soundness.witnessUndefined`, `trustedSat` respects it (§9.1 item 4); shared with noinit |
| 4 | depth | continuation is not a concrete walk; no failure rule | reach an exit with every predicate unsat, any other ending counts as undefined; static IR scan gate |
| 5 | depth, design | `SymexTargetKind` cases break; UB witness has no payload home | migration note; `undefined: seq[UbFinding[T]]` |
| 6 | depth | `feUnadmitted` as `dcOmitted` leaves the surviving path clean | `dcNoAnswer` until K7b drops the path |
| 7 | depth, design | a table does not prove a dispatch consults it | generated dispatch (`dispatchMagic`), arm ⇔ row checked at compile time; type-op verdict attached to the IR |
| 8 | depth | enum-keyed tables as `openArray` lookups | `array[K, …]`; `exact(...)` constructor rejects empty rows |
| 9 | depth | `querySetting` cannot see `--passC`, `-O`, compiler version | declared `-d:nelliFwrapv`; compiler family by `defined`, version a pin fact |
| 10 | depth | inlined stdlib body under a push | stdlib-body rows carry their check-option delta |
| 11 | depth | cell identity churns under refactor | cell = (axis, arm key); registered site strings |
| 12 | depth | §12 vacuous three ways | non-empty rows; precision non-regression item 5; pairwise floor from K8a's first run |
| 13 | depth | compile-only arm64/macOS cannot satisfy §12 | refused by name until run legs exist |
| 14 | depth | `skip()` not checkable against cells | `skip("cell:<axis>/<key>")` |
| 15 | design | `Admission[K]` is a row type, not a module | per-axis verbs, private rows, `Admit` answer, `Cell` enumerator (§8.1); old shape recorded in §13 |
| 16 | design | `proven(paths, pin)` reopens the hole | dropped; `halt` returns void; `walkUnsupported(): Survivors` |
| 17 | design | `$buildProfile` unstable; cc identity keyed | `cacheSegment` via `fieldPairs` + golden pins; semantic vs provenance fields |
| 18 | design | K9 a fourth lineage, arity-locked | grows `s8cu_helpers.nim`, on the splat, typed `Domain`, typed cell |
| 19 | design | float-to-int is a fresh symbol, not a halt | moves to the halt (K10a) |
| 20 | liveness | W1 pins written before K9 | K9a first in Wave 1 |
| 21 | liveness | K1 cannot read run-time `exhaustive`; shards split pins | pin records + post-shard K1 job |
| 22 | liveness | ratchet forbids introducing an axis | per-axis introduction rule |
| 23 | liveness | §5 rows and F ledger invisible to §12 | `Cell.items` + run-time id scan; §12 item 2 |
| 24 | liveness | fuzzer and scheduled legs have no failure consumer | issue per shape hash / per red run; §6 intake rule |
| 25 | liveness | MSVC shipping build has no row | `symex-msvc` in CI-B |
| 26 | liveness | refc refusal only in Wave 3; RFC-0014 pointer missing | refusal in W1-c1; SND-14 |
| 27 | liveness | older pending slices orphaned | "Carried slices" paragraph (§11) |
| 28 | liveness, feasibility | 0.9.2 gate undefined | sweeps c/cpp/4.13.4 at the W1-z sha vs a 0.9.1 baseline, Windows legs, wiring audit, code review |
| 29 | feasibility | W1-c and W1-d are rounds | split into c1/c2/c3 and d1/d2/d3; W-32 to Wave 4 |
| 30 | feasibility | W-06 has two sites; W-20 cite wrong; W-21 has a third site | corrected in the Wave-1 table |
| 31 | feasibility | second `nimPanics` read at `canonicalize.nim:6537` | rerouted in W1-c1 |
| 32 | feasibility | stale cache between W1 slices | bump in W1-a |
| 33 | feasibility | `verifiedLibs` needs a payload or absent-kind | ADM-1 decides; interface expected to change |
| 34 | feasibility | CI-A hides a known-red allowlist and provisioning | sized m-l with its parts listed |
| 35 | breadth | many W rows and §5 rows had no slice | §5.9; PRC-01/02 in Wave 3; K7 takes W-11/W-16; K5b takes W-58 |
| 36 | breadth | 0.10.0 migration note unnamed; second cold start | K10d writes it |
| 37 | breadth | §3.1 still said "tracked by rate" | restated; INF-03 rate report dropped |
| 38 | breadth | §5.1-§5.8 reconciliation | applied row by row (closes, merges, moves, SND-13/14, PRC-36/37, CRH-06..09) |

**Next:** `/tdd rfc-0016 wave 1`, starting with K9a. The RFC's `state` stays
`in-progress` (it was already past `ready` when RFC-0005's slices moved in).

## Round 3 ledger (2026-11-06)

Five Fable lenses on `9e275cf6`. Every point resolved by recommendation;
none reached Corey. Two looked like forks and are not: `-d:nelliFwrapv` can
produce `-fwrapv` itself (a global `{.passC.}`), which beats recording it as
an assumption; and 0.9.2's compile breaks follow 0.9.1's precedent of a
patch release whose migration note lists them (D-0016-5 stands).

| # | lens | finding | resolution |
|---|---|---|---|
| 1 | depth | UB disjunction solved at the survivor's exit is trivially unsat (the survivor carries `¬cond`) | §9.1 item 2: the undefined side is its own terminal path at the op, decided at the raise boundary |
| 2 | depth | an infeasible UB side inside a callee replays clean from the call cache | unsat side is `logPrune`d; `pruneFactsHold` guards reuse |
| 3 | depth | the three drains are gated on `arithChecks` and return `@[p]` clean | the UB sink is ungated; gated drains taint `feCheckOption` until K10d |
| 4 | depth | the whole-run gate scanned one `IRProc` | transitive over walked callees, unwalked calls answer "may be undefined"; reuses `scanOpaqueDefects` |
| 5 | depth | continuation unspecified | `wmFollowConcrete` with the model as `concreteEq`; undecided counts as undefined |
| 6 | depth | an untrusted UB witness would be host-run by `symexForAll`/`assertCoveredBy` | `hostRunnable` requires `witnessUndefined == {}` |
| 7 | depth | optional sixth cache field ambiguous with `runDependence` | version 4: six fixed fields, optional seventh |
| 8 | depth | `{.noinit.}` read has no per-path carrier | Wave 1 is run-level (`feNoinitRead`); per-path in K10b |
| 9 | depth | checks-off model keyed to a setting the build never sees; W1-d2 closed only the push route | W1-c1 carries check options; W1-d2 covers the settings route, *round*, last before W1-z |
| 10 | depth | W1-c1's pin narrower than §8.3 | pin covers `defined(nimPanics)` and `compileOption(` |
| 11 | depth | panics: defect-ness after handler search; bare `except:` on unknown type; W1-c3 dead under panics | all three in W1-c2's scope; W1-c3 pins panics-off only |
| 12 | depth | "row with no arm" checkable only per site | rows carry consuming sites; dispatch checks its own site |
| 13 | depth | `-d:nelliFwrapv` trusted, not enforced | the define emits `{.passC: "-fwrapv".}`; refused under `vcc` |
| 14 | depth | §12 item 5 not measurable by `sweep-diff.sh` | restated as a per-axis exact-cell ratchet plus kept 0.9.1 baselines |
| 15 | design | `pin` and `items` on `Cell` put test/RFC metadata in `src/` and duplicate the pin record | removed; RFC rows carry `cell:`; pin records are the only link |
| 16 | design | `site: string` has the wrong cardinality | per-axis site enums, `dispatchMagic(site: static …)`, census checks each once |
| 17 | design | `Axis` mixed admission, coverage and pin families | error-kind coverage is a K1 derivation; call-shape and exn × memory are test-side families |
| 18 | design | `amOutOfScope` as a consumer branch, with no kind | `Admit[P]` is admitted/not with payload; `Intent` is ledger-only |
| 19 | design | `admission.nim` placement misdescribed | above `types.nim`, Z3-free |
| 20 | design | `Survivors` underspecified | `halted`/`surviving`/`admittedExact`; end state every arm (K7c) |
| 21 | design | `runtime.nim:19172` records and continues | fourth shape: keeps its path through `taintInPlace` |
| 22 | design | `cell: static Cell` circular | pins name a `CellKey`, checked at compile time |
| 23 | design | `witnessUndefined: bool` loses the kind; not projected | `set[UbKind]`; `FindingUndefined` projection; `UbKind` not "class" |
| 24 | design | `stkUndefined` breaks more in-tree `case`s than cited | `wireTarget`/`unwireTarget` and four `bindSym` splices listed |
| 25 | design | `BuildProfile` field list plus assertion | split by type: `BuildSemantics`/`BuildProvenance` |
| 26 | design | `Soundness.profile` naming | `buildSegment` |
| 27 | breadth | CRH-01 contradicts C-06 (the `sort` stop is gone) | sort half to W-36; CRH-01 keeps the two unprobed stops |
| 28 | breadth | PRC-29 shard claim false | sharded at the median; measure it |
| 29 | breadth | stale cites INT-23, INT-25, INT-27 | re-cited |
| 30 | breadth | CRH-04, INT-20 missing their "Includes" | added |
| 31 | breadth | §5.0 and F ledger pointed at pre-split W1-c/W1-d | re-pointed |
| 32 | breadth | INT-33 used as a row and a slice id | slice renamed K8-0 |
| 33 | breadth, liveness | §5.9 ids invisible to K1's regex; "open" undefined | one id per row (MOV-01, STY-01..09); closed-state vocabulary in §5.0 and §8.2 |
| 34 | breadth | `(F-06)` in CI-A was a lens id | `(W-59)` |
| 35 | breadth | W-19, W-57, W-59, W-60, W-64, W-69 unhomed | homed in §5.9's preamble and rows; CI-C/CI-D in CI-B |
| 36 | breadth | sanitizer job, 132 assertions, 481 suites had no ids | K8c, K9c, K9d |
| 37 | breadth | `symexFind` off the main thread uncovered | §8.2 threads bullet: a build-axis cell pinned by the three isolation suites |
| 38 | breadth | concolic flip solve outside K10 | K10a scope |
| 39 | breadth, liveness, depth | MSVC absent from the 0.9.2 gate | W1-m runs `tsymex_0016_*` under vcc on `fuzzer-msvc` |
| 40 | breadth | `docs/symex/README.md` decline catalogue stale; new declines name no kind | W1-z rewrites it; each W1 RED names its kind; messages point at the README |
| 41 | breadth | four unlisted 0.9.2 compile breaks; no release per wave | Compile breaks section in W1-z; §11 Releases paragraph |
| 42 | breadth | publication steps absent | nimble bump, dry run, tag, registry check in 0.9.2's gate; W3-z for 0.10.0 |
| 43 | feasibility | K9a cannot type `Cell` before ADM-1; splat private; no crash pin | `static string` key until K9b; export `emitWitnessSplat`; `pinCrash` |
| 44 | feasibility | W1-d2 is a *round*: settings route and 13 files | scope and files below; last before W1-z |
| 45 | feasibility | W1-d3 threading cost | run-level in Wave 1 (row 8) |
| 46 | feasibility | cites: W1-e `:4126`, W1-f `:12789` | dropped / replaced by the three `case` sites |
| 47 | feasibility | no versioned Z3 4.13.4 tooling | INF-05 |
| 48 | feasibility | K1a is m-l | split K1a-test / K1a-ci |
| 49 | feasibility | Wave 1 order | K9a, W1-c3, W1-a, W1-c1, W1-c2, W1-b/e/f/g, W1-d1, W1-d3, INF-05, W1-m, W1-d2, W1-z |
| 50 | liveness | pin records unread for a release | K9a ships `pinRecords` and round-trips it |
| 51 | liveness | universe test races its pins inside `sweep.sh` | runs last over the record directory; records keyed by (file, segment) |
| 52 | liveness | K1a's post-shard job named no workflow; misses legs | K1a-ci lists the three workflows, depends on CI-B |
| 53 | liveness | ratchet rules not test-checkable | test checks membership and staleness; growth is a review rule |
| 54 | liveness | W1-d3 RED could pass vacuously | forced zero slot: `rsConfirmed and not trusted()` |
| 55 | liveness | issue sinks end at a person; schedules run `main` and die after 60 days | `rfc-0016-intake` label; `workflow_dispatch` `ref`; heartbeat; W2-z/W3-z/W4-z check them |
| 56 | liveness | per-build golden needs a selector | `defined(cpp)`/`defined(vcc)`/Z3 version |
| 57 | liveness | W-63 JIT row not in CI-B | closed against the Windows legs (PRC-27); K2a rechecks |
| 58 | liveness | pre-W1-z chores not in W1-z | UPS filing and MOV-01 in W1-z's RED |
| 59 | liveness | no Wave 4 tracker row; stale W1/W2/W3/S8ci/rv0005-lows titles | `W4` added; titles corrected |
| 60 | liveness | §12 items without a producer | each item names its slice; pairwise floor file (K8b); `.summary` in CI-A |
| 61 | liveness | `symex-mingw.yaml:217-230` cite is the Z3 install step | the cite was in the replaced §8.2 text; dropped |
| 62 | liveness | INF-04 item 10 "do not file" contradicts D-0016-3 | superseded note in §11 carried slices |

**W1-d2's files** (verdict-bearing `acOverflow` opt-outs, 13 of the 21 that
name `arithChecks`; round 3 said 19): `tsymex_161_overflow_obligation`,
`tsymex_163rev_concolic_modes`, `tsymex_163rev_inert_exclusions`,
`tsymex_phase16_R16_4_overflow`, `tsymex_phase2_overflow`,
`tsymex_phase3_summarization`, `tsymex_rfc0005_s8aa_remainder`,
`s8ac_remainder`, `s8ad_remainder`, `s8aj_remainder_c`, `s8cu_cl_over`,
`s8cu_push`, `s8w_remainder_b`. The other six pin settings shape or mention
it in a comment, and two (`tsymex_configdefaults`, `tentrypointwiring`) pin
the default `arithChecks`, which W1-d2 now derives from the build.

## Round 4 ledger (2026-11-07)

Five lenses (depth, breadth, design, feasibility, liveness). All findings
resolved by recommendation; no fork reached Corey.

| # | lens | finding | resolution |
|---|---|---|---|
| 1 | liveness | the property the RFC lives on was never stated; first end-to-end run at W4-z | §8 opening sentence; K1-0 runs it on the seven §5.0 cells in Wave 1 |
| 2 | breadth | no trust base: Z3 unsat, FFI, patched Nim and its VM, C compiler, unobservable C flags | §2.5 with a mitigation per row; the parser-VM cell in CI-B |
| 3 | design | `Admit` constructible anywhere; IR built without it | private fields, accessors; IR constructors take `Admit` (ADM-1 spikes `ensureProcRegistered`) |
| 4 | design | four declarations per axis | generic private `Row[S;P]`/`AxisTable[K;S;P]`; per-axis site enum, rows, verb |
| 5 | design | `CellKey` stringly typed | `(scope: Scope, key)`; key only from `render`; `magic(static string)` |
| 6 | design | `MagicShape` duplicates the definedness axis | dropped; magic keys on name, `OperandClass` only in definedness |
| 7 | breadth | no type-class axis (`NimTypeKind` × modifiers) | ninth axis `axTypeClass`, K3a; K2c corpus per `NimTypeKind` |
| 8 | breadth | generics have no home | `faGeneric` family (geUnresolvedGeneric, geInstantiationCapped, AUD-07) |
| 9 | breadth | pragma axis only local | three lists; `union`/`packed`/`byref`/`bycopy`; `noalias` as an `OperandClass` (K3c) |
| 10 | feasibility | `unsignedIntOps` (`dsl_parser.nim:11866`) a fifth magic table | in the magic axis's absorbs; the first converted site |
| 11 | depth | ledger parses markdown by regex | `docs/rfc-data/0016-worklist.toml`, rendered back with a staleness check (K1a-ids) |
| 12 | depth | records keyed by (file, segment): Z3 versions and reruns clobber | one file per run id; `rowOf` in the record |
| 13 | feasibility | `NELLI_PIN_DIR` does not reach the container; `.pins/` untracked | INF-05 forwards it; `.gitignore` |
| 14 | depth | an `exact` cell with no record on a leg passes | counts as unclassified there |
| 15 | depth | "only grows" checked by review | committed `0016-universe.tsv` diffed by the test |
| 16 | depth | closed and `never` rows unverified | closed names an exact/never cell or pin; never names a never cell |
| 17 | depth | declined-for-now cells count as done | `iModel` is open (§12 item 2); `NeverReason` enum |
| 18 | depth | bare `skip(` | `skipCell` writes a `skipped` record; census fails from Wave 4 (K2a-fail) |
| 19 | breadth | 17 caps have no coverage | `CapKind`, one halt site each (K7a); K1 derives coverage |
| 20 | feasibility | "about 90" error kinds | 81 |
| 21 | depth | PCRE and Z3 are run-time facts in a compile-time profile | `HostSemantics`, keyed (`pcre_engine.nim:93`, `canonicalize.nim:6645`) |
| 22 | design | `cpu`/`os` strings; endian unread; two names for the segment | enums; `endian` refused; one name `buildSegment` |
| 23 | depth | build-to-row mapping implicit | `rowOf` with per-field justifications; no row refuses |
| 24 | breadth | unobservable C flags | `assumedAbsent` provenance; `never(nrUnobservable)`; K10c `-ffp-contract=off` pin |
| 25 | depth | §8.3 said `check_options` rebases on the profile, which reopens W-07 | baseline stays `defaultOn`; W1-c1a moves only the reads |
| 26 | depth | `SymexSettings` keyed by a hand list | `fieldPairs` with an explicit neutral `const` (K5a), pinned in CR2 |
| 27 | depth | `pinCrash` probe loses `-d:` defines and the C compiler | inherits defines; `vcc` arm; flags in its record |
| 28 | design | `admittedExact` is a walker claim with no evidence | dropped; `exact` + K2 literal census; `continued` added for `:19172` |
| 29 | design | four pin verbs; `pinRaised` duplicates `pinExact` | three verbs; raise is a target; `PinVerdict` enum |
| 30 | depth | `pinCrash` records could evidence `exact` cells | only `declined` or `never`; exit class per OS |
| 31 | feasibility | `pinExact` needed exports from `symex.nim` | built on public `assertCoveredBy` + domain loop |
| 32 | feasibility | K9b retyped every Wave-1 key | K9a lands `CellKey` unchecked; axes switch their own keys |
| 33 | depth | UB beside taint, not through it | `Degrade.ub`, `Path.undefined` joined by carriers; contiguous `ub*` kinds and `UbKind` range; `feNoinitRead`/`feWitnessUndefined` dropped |
| 34 | depth | lazy decision at the boundary puts the prune outside the callee window | eager capped check at the op (`loopArmInfeasible` shape) |
| 35 | depth | `routeRaise` lets `except:`/`finally` consume UB | `haltUndefined`, sibling of `crashRaise`; `¬cond` in `pc` not `defectSurvivorPc` |
| 36 | depth | "opaque means may be undefined" untrusts nearly every sat | opaque answers by magic and stdlib-body rows |
| 37 | feasibility | no resume-from-label exists | second walk from the entry under the witness's choices; lossy counts as undefined; K10b a round with perf figure |
| 38 | depth | codec one char per field cannot hold a 5-member set | decimal of any length; `ord` pin; `runDependence` detection by length |
| 39 | depth | `{.noinit.}` recorded at allocation also hits written vars | at the read site (`unwrittenKind`/`observeRecvPart`), per path in W1-d3 |
| 40 | depth | three wrap readers can disagree (#161 shape) | one `buildWraps` predicate; `defaultSymexSettings` derives `arithChecks`; checks-off cfg suite |
| 41 | depth | Windows UB pin asserted only "did not finish" | exit class per OS |
| 42 | liveness | sat-after-label gap unlisted for 0.9.2 | named known gap in the migration note |
| 43 | breadth | entry points: four listed, six exist | `symexFindAllWitnesses` and the cache hit added |
| 44 | depth | wall-clock budgets flake exact pins | rlimit-only in `pinExact` |
| 45 | breadth | no metamorphic oracle | §10 relations; K8a-gen, K8b |
| 46 | breadth | pin strength unmeasured | K9e mutation figure |
| 47 | liveness | INF-05 after the slices that need its gate; baselines on one host | INF-05 first; baselines as `v0.9.1` release assets in `tests/0016-baselines.txt` |
| 48 | feasibility | W1-c1 touched five modules | W1-c1a (reads) and W1-c1b (reroutes, refusal) |
| 49 | feasibility | W1-c2 changed `hostRunnable` | uses `witnessUnsafe`; destructor gap named |
| 50 | liveness | W1-m dispatch and empty-glob | `workflow_dispatch` with ref; zero matches fail |
| 51 | liveness | SND-07, SND-12, INT-21 probe agreements unpinned | W1-p |
| 52 | feasibility | W1-d1 mixed three mechanisms | W1-d1a (signed), W1-d1b (unsigned sink and scan), W1-d1c (call cache) |
| 53 | feasibility | per-slice walker bumps unspecified | every verdict-bearing slice bumps, updates CR2:1103, adds a floor |
| 54 | feasibility | CI-A, K1a, K4a, K8a, K10a over three modules | split (CI-A1-3, K1a-cells/ids/last/ci, K4a-table/dispatch/guard, K8a-gen/job/sink, K10a-target/axis/float/concolic) |
| 55 | liveness | probes deferred to Wave 4 behind K4c | K2-0 probe batch in Wave 2 |
| 56 | liveness | `symexForAll`/concolic first pinned in Wave 4 | K9d-0 in Wave 2 |
| 57 | feasibility | K5a in Wave 3 though Wave 2 records need the profile | K5a first in Wave 2, emits `-fwrapv` |
| 58 | liveness | W2-z/W3-z checked presence, not content | nonzero records, cells, SUTs; per-axis exact cell and shrunk allowlist |
| 59 | breadth | hygiene rows homed "Wave 4" only | H1 |
| 60 | liveness | 16 research W ids invisible to the ledger | §5.9 rows W-08..W-61 |
| 61 | liveness | STY rows homed by prose | slice id as state; AUD-01/09/11 homed |
| 62 | depth | CRH-03 wholly moved | bounded decline stays as a declined cell; only the merge moves |
| 63 | breadth | §12 had no cost or docs item | items 7 (25% per leg, 60 s, minutes cap) and 8 (README names every kind) |
| 64 | breadth | alternatives unrecorded | §13: checks-off refusal (D-0016-9), always `-fwrapv`, second solver, EMI, mutation, UB-free generation, IR interpreter |
| 65 | feasibility | handoff said 19 files name `arithChecks` | 21; two pin the default |

**Next:** `/tdd rfc-0016 wave 1`, INF-05 first. The RFC is ready for `/tdd`;
`state` stays `in-progress`.
