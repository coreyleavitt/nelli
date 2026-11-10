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
- **Session state (2026-11-10):** Wave 3, slice 21/22 done, 1 remaining
  (W3-z, held by the wiring-audit gaps below); no forks open for Corey. main b2644983 (walker 311): PRC-07
  (e6b3362e), then PRC-02, PRC-02b, PRC-02m parts 1-3 and the PRC-07/08
  remainder (float checks, float `/=`, `-d:danger`, `math.ceilDiv`,
  nilChecks n/a), symex-linux 42758660494 and symex-mingw 42758660691 green.
  In flight:
  - `rfc-0016-msvcshard` 0cd412ac: the MSVC leg in 5 walker shards (46 min
    wall against the 90 min timeout); k5b fwrapv asserts the vcc refusal;
    the fieldoff probe accepts a refuted indeterminate read under vcc only.
    fuzzer-msvc run 42760274142 in flight; land when green (main's MSVC leg
    is red on that probe until then).
  - BLOCKED on Corey: Nim fork patch 0009 (f27f1b164, subtype-hook table)
    cannot republish; dispatch returns "Actions has been disabled for this
    repository" while the permissions API reports enabled. Until then nelli
    CI exercises the table-less pins.
  - W3-z /wiring-audit (2026-11-10, worktree at e707b09c, 3 opus lenses)
    found gaps, so W3-z is NOT taggable yet. Soundness first:
    U1 replay-confirmed sat candidates skip `verifyTailDefined`
    (`runtime.nim:30384`, `symex.nim:3551-3604`); U2 `opaqueUndefined` is
    read only by the tail walk (`runtime.nim:19747`), so `tUndefined` can
    return a trusted unsat; U3 `tUndefined` can never hit
    `ubIndeterminateRead`. Evidence side: F1 the W3-z per-axis check does
    not exist (construct/readonly axes have 0 cells); F2 K6 tests write no
    pin records; F3 `joinIds` checks only open rows; F4 the join ignores
    verdict versus cell state. Also: concolic float-to-int bypasses
    `decideUndefined`, `fromFlip` ignores `undefinedReached`, freshness and
    dead-leg checks never fire, the F-ledger is frozen at 7 rows, docs-only
    pushes skip the evidence gates, and allowlists grew. The full list is
    in the scratchpad `wa3-findings.md`; the admission/BuildProfile lens is
    still out. Next: verify, slice and fix, then /code-review, then tag.
  - Resume: re-read this block and the scratchpad `restack-todo.md`; land
    msvcshard via the `$S/hand` protocol (push to main in a separate call),
    then /wiring-audit and /code-review for W3-z.
- **Session state (2026-11-09):** Wave 3, slice 18/22 done, 4 remaining
  (PRC-07, PRC-02/02b, PRC-07/08 remainder, W3-z); no forks open for Corey.
  main 6490a48b (walker 308). In flight:
  - PRC-07 `rfc-0016-rangeoff` (walker 309): the union image carries an
    indeterminate-byte mask (f8c76b11; a callee-built hit follows the
    `{.noinit.}` replay convention) and is gated on `supportsCopyMem`
    (0d5bcd81, `IRType.vNoCopyMem`). Next: ref variants, then land via CI.
  - PRC-02 `rfc-0016-prc02` 35ad0c27 and PRC-02b `rfc-0016-prc02b` d8951308
    (both still say walker 308; rebase onto main after rangeoff, renumber to
    310). The Nim fork `toolchain` was fast-forwarded to f7b3a6170 (patch
    0008: a per-executable method dispatch table, hidden visibility);
    republish runs in flight; old artifact digests saved for rollback.
  - Open follow-ups: `symexFind` over a method SUT is `sxUnknown`
    (`feGlobalRouteUnproved`); the cpp "nimcall-typed global" pin in
    `tsymex_0016_prc02_reexec` fails `feHostUnadmitted` under both compilers;
    tail-walk witness loop count above `maxLoopUnwind` fails closed.
  - PRC-02m `rfc-0016-prc02m` (walker 310, comment extended): under
    `hasMethodTable` the route scan reads a dispatched method's registered
    overrides as callees (a hypothesis at macro time) and the entry's route
    list is wrapped in `methodRouteGuard`, which asks the run's table and adds
    a `!` route (every variable read declines) when a body outside the scan
    can run. This closes an unsound trusted `sxUnsat` for a hidden override
    (`tsymex_0016_prc02m_find`). BLOCKER for the `feGlobalRouteUnproved`
    follow-up: it is not the method open alone. `routeType` opens every global
    for any `ref` of an inheritance hierarchy ("may hold a subtype, whose
    lifetime hooks cannot be listed"), and the table lists method receivers,
    not subtypes, so a global read beside a method SUT still declines. Stock
    builds still trust a hidden override when the SUT reads no global.
    (That last line was closed by db30cbf6: without the table every method
    dispatch declines.)
  - PRC-02m part 3 (walker 310, comment extended): the blocker above is
    closed under the toolchain's subtype-hook table (Nim fork patch 0009,
    `nimHasSubtypeHookTable`, `nimSubtypeHookTable`: per proper ancestor of
    every inheriting object type the binary writes a header for, each user
    lifetime hook a value of the subtype may run, transitively through what
    it holds; a closure field marks the row open). `routeType` records the
    hierarchy's `module.Type` instead of opening every global, and
    `subtypeRouteGuard` (`replayproc.nim`) adds the `!` route when a subtype
    in the binary has a hook outside the hooks the scan read. A global read
    beside a method SUT now decides (`sxSat`, witness 9); a subtype built only
    at module init with a `=destroy` still declines. Generic-instance bases
    and table-less builds keep "may hold a subtype". The patched compiler
    must be republished (fork `toolchain`, patch 0009) before CI sees it;
    until then CI runs the table-less pins.
  - Resume: `/loop implement the next unimplemented rfc-0016 slice with /tdd ...`
    (the standing prompt); re-read this file and MEMORY.md first.
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
  K3c (`rfc-0016-k3c`, walker 293 to 294): `smt/pragmaaxes.nim`'s
  `pragmaAxis` is the pragma axis, rows keyed `<place>/<name>` (`local/`,
  `routine/`, `param/`, `type/`) on the `pragma:` scope, so W1-b's
  `pragma:local/cursor` pins are its cells. `admitPragma(place, name, site)`
  is read at the local declaration (replaces `localPragmaAllowlist`), at
  `ensureProcRegistered` (a routine pragma, a formal's pragma, and each
  formal and result type), at the local-declaration type gate and at the
  target's own formals (`parseProc`). `union`, `packed`, `byref`, `bycopy`
  on a type, `byref`, `bycopy`, `noalias` on a parameter, decline
  `feUnsupportedOp` (a type is looked through fields, tuples, distinct, ref,
  ptr and generic arguments); a routine pragma with no row declines
  `feUnadmitted`. The lib-wide guard (`tsymex_0016_k3c_pragmaaxis`) fails on
  a pragma `lib/` spells that has no row in any place (pragmas.nim is not in
  the toolchain image, so lib/ is the text scanned). A module-level
  variable the SUT or a callee names is checked as a local is, at the end of
  `parseProc` over `seenModuleGlobals()` (pinned by `tsymex_0016_k3c_pragmaaxis`:
  union and packed globals, and a union global reached only through a callee).
  Open: K8b exercises the unpinned cells (allowlisted in `pragma.txt`).
  K4a-dispatch (`rfc-0016-k4ad`, walker 294 to 295, renumbered at landing):
  `magic_rows.nim`'s `dispatchMagic` macro checks a site's `case` against the
  table at compile time (an arm with no row or a row not admitted at the
  site, a row admitted at the site with no arm, no `else`, and a second
  expansion of a site are errors) and records the site in a `{.compileTime.}`
  registry (`dispatchedMagicSites()`; the pin file asserts it equals
  `magicDispatchSites`). The sites are `msVarStmt` (`parseVarMagicStmt`),
  `msCallSwitch` (the stdlib call switch), `msInfix` (the unsigned operators
  spelled infix) and `msNewString`; `msProcRegister` is read with
  `admitMagic` (a stub-bodied magic or a `var`-formal magic declines with the
  row's kind, `feUnadmitted` for a magic with no row) and `msArm` names no
  place. `varParamMagics`, `VarMagicSite`, `VarMagicModel` and
  `unsignedIntOps` are gone: `+%`, `-%`, `*%`, `/%`, `%%`, `<%`, `<=%` are
  rows of the magic axis (they are `system` routines, not magics; K4c's
  stdlib-body axis may take them). Not converted: the opaque-call defect
  scan's four arrays (K4a-guard), `cgMutatingMagics` (a write-set property,
  K6), the `repr` magic list and the `IsNil`/`ProcCall`/`Move` equality
  tests (single-name checks inside other conditions). `tsymex_0016_k4a_dispatch`
  pins 87 `magic:` cells through `symexFind` (80 of the 242 allowlisted, plus
  the seven new unsigned-operator rows); the allowlist is 162: 110 cells no
  SUT reaches stay with K4a-dispatch (27 folded, 82 compile-time, macro or
  DrNim magics, and `nextafter`, which std/math does not export), and 52
  reachable ones (modelled, declined, unverified, bodied) are re-owned to
  K4b, whose round pins each.
  K4a-guard (`rfc-0016-k4ag`, walker stays 295): the opaque-call defect scan
  reads the magic axis. Which Defect a magic raises is a property of its row,
  four more `MagicSite`s (`msDefOverflow`, `msDefDivZero`, `msDefRange`,
  `msDefFloat`, `magicDefectSites`) read with `admitMagic`; `overflowMagics`,
  `divMagics`, `rangeMagics` and `floatArithMagics` are gone. `AddI64`,
  `SubI64`, `MulI64`, `DivI64`, `ModI64` were on the old lists but are not
  `TMagic` members in Nim 2.2.10 (no row, never matched). The guard is the
  K4a-table lib-wide row guard (a magic the scan meets has a row) plus
  `tsymex_0016_k4a_guard`, which pins each site's rows and that no unsigned
  divisor, refused or absent magic carries a defect. No allowlist entry was
  owned by K4a-guard; `cgMutatingMagics` and the `repr` list stay (K6).
  K4b (`rfc-0016-k4b`, walker stays 295): a bodied magic is walked through its
  Nim body only where its row is admitted at the new `msBodyWalk` (the three
  `mmBody` rows: `AbsI`, `MinI`, `MaxI`). `ensureProcRegistered`
  reads it after the stub-body decline: any other row declines with its kind
  (a modelled or partial row is `feUnsupportedOp`: the body was being inlined
  as the semantics, e.g. a `succ` whose body is `x + 1000`), a magic with no
  row `feUnadmitted` (no SUT can show that one: an unknown magic name crashes
  the Nim compiler). `tsymex_0016_k4b` pins both outcomes through `symexFind`
  with user routines carrying `{.magic.}` and a body; `tsymex_0016_k4b_cells`
  pins 48 of the 52 re-owned `magic:` cells (one SUT per cell:
  exact for the 28 modelled or walker-handled, decline for the rest). Four
  stay allowlisted, under K4a-dispatch, each with a reason: `DeepCopy`
  (needs `--deepcopy:on`), `ShallowCopy` (not declared under orc),
  `NewFinalize` (orc finalizers are `=destroy`-shaped), `GetTypeInfoV2`
  (`getDynamicTypeInfo` is not exported). `GCref` declines
  `feUnsupportedExprKind` at the type bridge (`RefHeader`'s `when`), not at
  the row. The row states follow the pins: `Dup`, `Slice`, `EqProc`,
  `EqCString`, `Fields` and `FieldPairs` were partial, body or unverified and
  pin exact, so they are now `mmModelled` (`EqCString`'s importc `cmpStrings`
  body is never walked: the cstring operands cross as strings, so it left
  `msBodyWalk`). The last suite of `tsymex_0016_k4b_cells` is the drift
  guard: every cell pinned exact has an admitted `mmModelled`/`mmFolded`/
  `mmBody` row (never partial, never refused), and a decline pin on an
  admitted row only on a partial or folded one.
  PRC-01 (`rfc-0016-prc01`, walker 295 to 296, with INT-01 and INT-14): the
  re-exec path already carried the solver's model for a `symexFind` witness, so
  a case object, `ref` (identity kept) or `ptr` parameter replayed on every
  leg. What declined was the wire itself: `replaywire.nim` refused a case
  object statically, so a module-level variable of case type, and a typed
  witness given to `replayWitness`, declined. It now writes the discriminator
  then the active branch and reads it back with `reset` + `uncheckedAssign`
  (`isWireableType` walks `nnkRecCase`). A non-nil `ptr`, `pointer` or
  `cstring` in a global or typed witness still declines, now naming which: its
  target (a variable, a field, C memory) cannot be given to the child and a
  fresh cell would drop the aliasing. `tests/tsymex_0016_prc01_reexec.nim`
  (re-exec on Linux via its `.cfg`) pins case-object globals (both arms), a
  case-object and an aliased-`ref` witness through `replayWitness`, a SUT with
  type symbols in its footprint, and the `ptr` decline.
  K4c (`rfc-0016-k4c`, walker 296 to 297): `smt/stdlib_rows.nim`
  holds the stdlib-body axis (`stdlibAxis`, key `<module>.<name>[/<facet>]`,
  `admitStdlibBody`). Walked rows carry their check-option delta (`exercises`);
  `applyStdlibDelta` (dsl_parser) reads it for a routine whose options deviate:
  an option the body cannot trip is no deviation, and `overflowChecks` that it
  trips is modelled (`ArithScope.asUnchecked`, `RoutineChecks.overflowModelled`:
  signed overflow and a zero divisor are `ArithTrap`s, as in a checks-off build)
  instead of declining. Rows: `math.isPowerOfTwo`, `floorDiv`, `floorMod`,
  `euclDiv`, `euclMod`, `nextPowerOfTwo`, `sgn`. PRC-09 is closed: every routine
  of math.nim's `checks: off` region (157-1116) has a row. `ceilDiv`
  (unsigned conversions, `feCheckOption`) and `divmod` (opaque tuple generic,
  `feOpaqueCallUnmodelled`) are declined rows. A float-first call is never
  walked by body (`mathInterception` lowers it by name): `sqrt`, `floor`,
  `ceil`, `trunc`, `round`, `signbit`, `isNaN`, `copySign`, `classify` are
  modelled rows, every libm function and composition plus `frexp`,
  `splitDecimal`, `degToRad`, `radToDeg`, `almostEqual`, float `mod` and
  `round(x, places)` are declined rows (`feUnsupportedOpAborted`, the cell
  named). `round` was banker's rounding and is now ties-away-from-zero (C
  `round`); float `mod` was an internal walker fault and is now that decline.
  The JS-only and CC89-only helpers of the region (`toBitsImpl`, `jsSetSign`,
  `truncImpl`, `log2Impl`, `jsRound`) get no row: no build row compiles them.
  The absent-row rule (RFC 8.1: a stdlib body with no row and no deviation is
  a decline): a routine outside `stdlibAxis` is `feUnadmitted` unless the
  corpus ledger (`smt/stdlib_ledger.nim`, GENERATED by
  `scripts/stdlib-ledger.sh` from a compile-only run of the suite under
  `-d:nelliStdlibLedger`) lists it as walked by the suite; `applyStdlibDelta`
  reads both. The ledger is seeded from the full corpus at 07dc23ab (all 1055
  `tests/t*.nim`, compile-only): 113 keys. PRC-07 is NOT done here: the RFC assigns its mechanism to
  K10a/K5a (K5a done; K10a-axis/K10a-float pending; W-34 depends on it).
  The seven unsigned operators moved from
  `magicAxis` to `stdlibAxis` (`system.+%` ...; they are `system` routines):
  `dispatchMagic` checks the `msCallSwitch` and `msInfix` cases against both
  tables; their pins are `stdlib:` cells now. W-47: the four stdlib generic
  objects are `declined` rows read by `classifyType`'s catch-all (a head with
  no row is the absent case, same kind; the decline names the cell). STY-02:
  `tables.Table/iterationOrder` and `sets.HashSet/iterationOrder` are `never`
  rows the declines name. STY-06: `algorithm.sort/symbolicLength` (named by the
  `#hook` decline), `typedthreads.createThread/concurrency` and
  `unicode.toLower/fullCaseFold` are `never` rows; the last two now decline
  at the call (`callDeclines`, `ensureProcRegistered`), naming the cell, and
  the allowlist is empty (`tsymex_0016_k4c_never`). AUD-11 is the
  `strutils.rfind/indexofLink` cell, pinned exact. Pins: `tsymex_0016_k4c`
  (rows, four routines exact, the delta both ways, rows-absent control),
  `tsymex_0016_k4c_off` (same under `--overflowChecks:off`),
  `tsymex_0016_k4c_cells`, `tsymex_0016_k4c_math`, `tsymex_0016_k4c_never`.
  FINDING (blocker, not fixed): `unicode.toLower(Rune(a))` with a symbolic rune
  does not terminate in 900 s. Probes: one binary search over a large const
  table stops at `maxLoopUnwind=5` in about 30 s (`beBudgetExhausted`); two
  sequential searches of a 450-entry stride-3 table hang with
  `maxFrontierSize=32`, with `queryTimeoutMs=20000`, and at default. No cap in
  this base covers it (`walkRLimit` is not in this base, so K2c's cap is not
  the cover), so it is a walker-side non-termination, not a slow Z3 query:
  the query timeout does not bound it. `toLower` is therefore declined at the
  call by its `never` row rather than walked; the hang itself needs a
  K2c-style cap on whatever the second search multiplies.
  K3b (`rfc-0016-k3b`, walker unchanged): the `fieldDefault` operation joins
  the type x memory-op axis (`typeop:fieldDefault/<IR kind>`, payload
  `ZeroModel`: literal, `iekZeroValue`, or the distinct's base; `itUninterp`
  is a refused row). `zeroValueForType` reads it, so a new `IRTypeKind` or a
  changed row moves the zero. A field's `= default` is never applied on the
  zero side (Nim writes it into `default(T)`, `T()` and `new`); `wasMoved`,
  `reset` and `move` are pinned at the bitwise zero for int, float, string,
  seq and tuple fields. `routeScan` no longer asks for the type of an untyped
  callee symbol (`wasMoved`'s own `=wasMoved(obj)` in a generic body was a hard
  "node has no type" error). W-12 closed.
  K2c (`rfc-0016-k2c`, walker 297 to 298): `classifyType`
  reads the type-class axis. New site `tcClassify` (kinds that become an IR
  type); `admitTypeFeature` reads the named rows. `owned T` and `Atomic[T]`
  read their `never` rows; a top-level `Atomic`/`owned` parameter was a compile
  stop (`emitTyAndReader` raised on `__ownership:`, CRH-01) and now declines
  `heUnsupportedOwnership`. `c_longdouble`/`clongdouble` reads the `float128`
  row and declines `feUnsupportedParamType` (it was modelled as a double, STY-06).
  An enum-indexed array (`classifyArrayBracket`) and an omitted variant field
  (`omittedFieldFeature`, the A1 constructor path) read their rows. The corpus is
  `tests/tsymex_0016_k2c_typeclass.nim`: one pinned snippet per kind a parameter
  can have (38 cells leave `typeclass.txt`). Remaining there: `K4c` owns
  `float/sNaNPayload` (a bit-pattern cast, not a type); the rest is `W4-z` (kinds
  no parameter can have). `pointer`, `varargs`, `UncheckedArray` (declines), `ptr`,
  `openArray`, `var` (modelled) are now in the corpus; `openArray` was a compile
  stop (replay splat bound `var p: openArray`), an object with a `pointer` or
  `UncheckedArray` field another (witness `int` placeholder in the slot; a flexible
  array member in a witness tuple). CRH-01 re-probed: HRV-44 is gone (pinned);
  `splitLines` was `classifyType` on an empty-typed iterator formal (`keepEol = false`),
  fixed, declines over a bounded string (pinned); over an UNBOUNDED string it ended in
  a typed `ckWalkWork` cap once K7 landed (below), so CRH-01 is closed. The `case n.kind` census row in
  `dsl_typebridge.nim` is not converted: K2c adds no dispatch to it.
  K7 hang, FIXED by the walker-side charge (`rfc-0016-k7charge`, walker 305; finding from `rfc-0016-k7hang`): two sequential binary searches over a
  450-entry const table (`unicode.toLower`'s shape; `tests/tsymex_0016_k7_twosearch.nim`) DO end
  as `ckWalkWork` under an explicit `walkRLimit`, but 20M units took 190-260 s, ~88k units/s
  against ~1M/s for arithmetic: the default 1e9 is hours. Wall time is walker-side, not Z3
  (of 258 s: Z3 `check` 3.6 s; own-context query build/translate 49 s; `divRangeFacts` 36 s,
  `bvOffsetLinks` 15 s, `bvIntInverseFacts` 16 s, `mergeMemberships` ~51 s, `seqLenCaps` 19 s,
  all inside `checkExact`). Each query is ~2000 DAG terms (8.66M terms over 4029 checks): the
  path condition carries each table as a 450-deep `store` chain (`select(store(...))`, 1.4 MB as
  text, DAG-shared), re-walked by about ten per-query passes. Paths stay few (max 64, usually 1-2),
  so it is per-query cost, not path explosion. Units did not see it: each query is ~5k units.
  Fix: `walkerWorkUnits` charges `walkerTermUnits` (15) units per term visit of
  `ownContextSolver`'s build and of each fact pass to the same `walkRLimit`
  spend (`walkUnitsSpent`); rate calibration is the comment by the constant
  (Z3 0.254 us/unit on three arithmetic suites, 4.0 us/visit on twosearch).
  The 1e9 default is NOT changed: re-measure it on the suite from this branch.
  Collect with `NELLI_WALK_UNITS_LOG=<abs file>` (dt-bounded.sh forwards it):
  `<units>\t<target>\t<status>\t<walker>`, `units` the whole spend now
  (Z3 + charge), `walker` its charge share (4th column, new). Decided walks
  that were table-heavy spend more than before (`splitlines_unbounded` still
  ends `ckWalkWork` at its explicit 20M, 15.4M of it charge).
  K7 total work (`rfc-0016-k2c`, walker 298, with K2c): `budget.walkRLimit`
  bounds the Z3 units of every check of one walk (`ownContextCheck` charges,
  `checkCapped` runs each query under what is left, `shouldStop` ends the walk,
  `runSymexImpl` records the one `ckWalkWork` halt as `beBudgetExhaustedPrune`).
  `NELLI_WALK_UNITS_LOG=<file>` appends `<units>\t<target>\t<status>\t<walker charge>` per walk
  (`dt-bounded.sh` forwards it). DEFAULT `1_000_000_000` (0 opts out),
  measured 2026-11-09 at d5d1d563 over the whole suite (1047 files, 7818 walks,
  eos): largest decided walk 175,310,967 units (`label:prod12`, sxSat,
  `tests/tsymex_augmented_assign.nim`), then 25,590,064 (`label:wrapped`),
  20,955,494 (`label:s8cj_wide_factoring`, sxRaised); largest overall 175.3M,
  then 120,601,918 (`label:ti_tuple`) and 103,233,480 (`label:t`), both
  sxUnknown. So the default is about 5.7x the largest decided walk and no
  decided verdict in the corpus is lost to it. `prod12` decides under the
  default with no override (`tsymex_augmented_assign` green, 381 s).
  `tsymex_0016_k7_splitlines_unbounded` (registered) KEEPS its explicit 20M
  limit: at the default the walk was still running at the dt-bounded 900 s kill
  (rc=137). Units vs wall time: the 20M-limit run consumed 20,033,527 units per
  walk, two walks in 278 s including a ~40 s compile, so about 118 s per walk,
  about 170,000 units/s; the default cap on this walk would take about 5,900 s
  (98 min). The cap bounds work, not wall time, and a `queryTimeoutMs` or
  harness timeout still ends a walk first. CRH-01 closed (pins:
  `k7_splitlines_unbounded`, `augmented_assign`, `k2c_typeclass`).
  K6a (`rfc-0016-k6a`, walker 298->299; W-08 closed): `mayWrite(n)` in
  `dsl_parser.nim` replaces `nodeWritesHeap` / `routineWritesHeap`. It is an
  allowlist of read-only node kinds (`mayWriteReadOnlyKinds`); every other
  kind (asm, a `cast`, a lambda, ...) and an `emit` pragma read as may-write.
  A call: a proc value, a method, a bodiless/importc routine, a stdlib routine
  given a `ptr`/`pointer`/`cstring`/`ref`/proc argument, and a `var` actual
  (or `mayWriteMagics` first argument, i.e. `cgMutatingMagics` minus `Addr`
  plus `Swap`) whose lvalue is behind a pointer all may write; a walked user
  callee is analysed by its body with a cycle bound (a cycle, or depth 64,
  answers may-write; the old `seen` list answered "no write"). Its only
  consumer is `mayWriteRoot`'s pointer branch (the S8cn `lent`/`let`
  decline). `cgMutatingMagics` itself stays for `cgPotentialWrites` (a
  different predicate: root symbols); K4a-dispatch's move of that list will
  need `mayWriteMagics` to follow. Pins: `tests/tsymex_0016_k6a_maywrite.nim`
  (12 may-write shapes with native runs, 5 read-only). Not done (remainder):
  K6b hook copy-proof (W-09/W-10), K6c `ptrUsesStayLocal` /
  `routeStoresThroughDeref` / `bindsViewWhole`; `scanOpaqueEffects` is still
  a separate scanner (D-05's "one rule" is not yet one function).
  K6b (`rfc-0016-k6b`, walker 299, extends K6a's; W-09 closed): the hook
  copy-proof `routeHookCopies` is fail-closed. A field copy `dst.f = src.f`
  counts only as a top-level statement of the hook body; every other
  statement must not name the destination, hold a `return` / `raise`, or
  `mayWrite`. Before, a copy under an `if`, behind an early `return` or
  followed by `zap(a)` (a `var` parameter passed on has no `nnkHiddenAddr`)
  was proved the plain copy and the walk decided it (false `sxUnsat`); an
  `emit` after the copy already declined, through the effect summary. D-05
  is not a worklist row: `foreignWriteNode` (asm, cast, `emit`) and
  `opaqueRoutine` (method, bodiless) are now the one judgement
  `scanOpaqueEffects` and `mayWrite` both call; the scanner stays a
  separate summary (it names which globals and heap types, `mayWrite` only
  whether), so its `ref`-argument and read-of-a-global rules are not
  `mayWrite`'s. W-10 stays open (home K6c). Pins:
  `tests/tsymex_0016_k6b_hookcopy.nim`. `tsymex_0016_k6a_maywrite` exits 0
  on c and cpp under `dt-bounded.sh` (the non-zero exit K6a's agent saw did
  not reproduce).
  K6c (`rfc-0016-k6c`, walker 299, extends K6a/b's; W-10 closed):
  `routeStoresThroughDeref` is now `routineMayWrite` (the one rule; `mayWrite`'s
  stdlib-argument rule takes `argHoldsCell`, the union of the two scans it
  replaces, and exempts a lifetime hook, which `readHooks` walks as its own).
  `bindsViewWhole`'s `else: discard` is an exhaustive `case` over
  `IRStmtKind` (a new kind must decide). `ptrUsesStayLocal` is an escape
  predicate sharing D-05's foreign-write facts (`foreignWriteNode`,
  `opaqueRoutine`) rather than built over `mayWrite`: a store of the pointer
  to a global by name is an escape and not a `mayWrite` question. It is
  fail-closed: an exhaustive `case` with no `else`, so an address taken
  through a deref (`addr p[].a`), returned by a callee (`addr x` of a `var`
  formal, `viewFormalStaysLocal`), passed to an opaque or non-magic callee, or
  a pointer inside asm/`cast`/`emit` escapes by the predicate itself, no
  longer masked by the `nnkAddr` gate. Focused test of the predicate:
  `formalStaysLocal` in `tests/tsymex_0016_k6c_round.nim` (internal style of
  `tsymex_0016_k4a_table`). No SUT gave any of the three a false
  trusted verdict: `addr p[].f` and a `var` actual returning its address are
  declined earlier (`feUnsupportedExprKind` on `nnkAddr`), a `var c = t`, a
  `lent` loop and a `lent`-returning call are declined, a tuple built from the
  container is a copy and decided. So `tests/tsymex_0016_k6c_round.nim` pins
  precision and declines with native runs, no RED. Open: `scanOpaqueEffects`
  is still a separate summary.
  Chain note (int4a): `smt/stdlib_ledger.nim` was seeded by K4c at 07dc23ab on an older
  main; K3b, K2c and K6 add no stdlib bodies. Reseed it (`scripts/stdlib-ledger.sh`) if
  the CI corpus run shows `feUnadmitted` stdlib declines.
  int4a CI fixes (symex-linux 42619836822, symex-mingw 42619836849): four
  `errorkind` allowlist entries removed (now pin-evidenced); a footprint scan
  skips an untyped call head (`getTypeImpl` "node has no type" on a re-executed
  replay, Windows-only; reproduced with `dt-crosswin.sh`); K3b pins all 11
  other modelled `fieldDefault` cells and the `uninterp` decline; W-19b
  `createThread` now asserts K4c's call-site decline; k7 splitLines budget
  re-derived (4M units, measured rates in the test); S6a counts 2 Prune sites
  (K7's `ckWalkWork` halt, audited dcOmitted); configdefaults override sets
  `walkRLimit`, ResourceBudget count 17 (merge line already in `+`). Walker
  stays 299. `s8cn_step1d` is red on Linux CI only: the known INT-43 Z3 5.1.0
  rlimit skew (`linux-host-known-red.txt`).
  int5 (`rfc-0016-int5` on main ad93de7f, walker 299 to 305): the int4b stack
  (K10a family 300, K10b 301, K10d 302, ADM-IR 303, K10b precision 304) rebased onto
  int4a's CI fixes, then `rfc-0016-cigate` and K7 charging (305, was 300 on its
  branch). Configdefaults: ResourceBudget 17 (K7), SymexSettings 8 (K10b added
  `wholeRunDefinedness`, K10d removed `arithChecks`); S6a counts 2 Prune sites.
  K10d follow-up: `tests/tsymex_0016_k10d_drain_checksoff.nim` pins that, in an
  `--overflowChecks:off` build, nothing forks an `OverflowDefect` (int8 wrap defined,
  int wide overflow is the axis's halt only). The drain's own gate is not reachable alone
  (the deposit site is already decided by the axis), so RED was shown by breaking both
  layers. The 0.10.0 migration note records the walker-work charge and the spend log's
  4th column. PENDING: the default `walkRLimit` (1e9) re-measure under the charge; the
  control loop is measuring it on eos.
  int5 CI fix (walker 305 to 306): the universe join failed on `typeclass:set`
  and five cells after it because `tsymex_0016_k2c_typeclass` failed at `set`
  (`pinExact`: sxSat not trusted). K10b's `modelPins` ran `svFitsHeapTy` on a
  `set[E]` parameter (`svBitSet`, which that heap-cell test does not name), so
  its pins were incomplete and the lossy winner failed closed
  (`ubTailUnverified`); the rest of the test's records were never written.
  `modelPins` now pins a builtin set parameter by its bit-vector. The mingw
  join also named `defined:read/uninitialised` and `errorkind:ubIndeterminateRead`
  (the `{.noinit.}` pin is skipped on a re-exec replay), allowlisted
  `rows=mingw,msvc,linux-cpp`, linux-c evidencing both.
  int5 CI fixes (walker 306 to 307): `tsymex_r6_n13_reassign_seqarm` went sxRaised
  because `modelPins` (a variant parameter's leaf split) and the tail walk recorded
  `seUnsupportedCompoundSortLeaf` in `loweringDegradeErrors`, which the explore verdict
  then drained; both now restore the sink and a degrade leaves the pins incomplete.
  `tsymex_0016_s8cj_runctx` FIXED (walker 307 to 308): the context was held by
  `currentCallerPc` / `closureBodyCallerPc` (run-state threadvars of Z3 terms) that the
  tail check's walk leaves non-empty; `runSymex` now empties both at the run boundary.
  The `modelPins` constant loop was a red herring (it only changed what the tail walk
  saw). `modelPins` is now driven from the winning path's own heaps (`heap_<key>` and
  its havoc epochs, `heapEpochCount`) instead of every model constant, so a havoc copy
  (`@hv`) is no longer pinned.
  `tsymex_0016_wa_checksoff` S1 bounds `n` (the model's 2^62 trips cannot be
  followed, fail closed by design); `tsymex_rfc0005_s8bm_stability` names the target query
  by its search, the tail walk appending a cheap query after it; the A2a marker is back on
  its call line. Witness pins are dropped from every result at the run boundary.
  PRC-07 range half (`rfc-0016-rangeoff` on `rfc-0016-int5`, walker 308->309): a
  `--rangeChecks:off` build is walked as compiled, no `feCheckOption` for the
  build's own bit (`RoutineChecks.rangeOn`; a push back to `on` declines).
  Native (generated C): int8/int32 narrowing and `chr` truncate, a range/enum
  conversion keeps the value, unsigned narrowing is unchecked in every build:
  all defined, exact. An array indexed by its own range/enum type has no check
  emitted, so an out-of-range value is an out-of-array access (UB in C):
  declined where reachable (`isIndex.ixUnchecked`, `isIndexAssign.iaUnchecked`).
  PRC-07 definedness half (same branch, walker 306 kept, unreleased): that access
  is `ubArrayOutOfBounds` (appended LAST in the `ub*` range, after
  `ubTailUnverified`; `UbKind = range[ubUnsignedDivZero .. ubArrayOutOfBounds]`;
  the codec stores `ord - ord(low)` bits, so no `soundnessMetaVersion` bump),
  row `defined:index/unchecked` (`aoIndex`/`ocUncheckedAccess`/`dsIndex`, undefined
  under every profile: whether a site is unchecked is the build's option, not the
  arithmetic profile). One decision proc, `decideUndefined` (runtime.nim, factored
  out of `drainArithTraps`, which now calls it), is shared by the index sites:
  `indexOobSide` (seq read/write, array read/write; `ixUnchecked`/`iaUnchecked`
  stay the parser's own-type-under-rangeChecks-off flag), the string arm, `pop`,
  the string-index and seq-OOB raise drains (`genRaiseForkDrain`'s `boundSite`),
  and `depositStrIndexOob` (`s[i]` / `s[i] = c` lowered in an expression deposit an
  `ArithTrap` with the kind). With the walker's `boundsUnchecked()` (the build's
  `coBound`) false everything is the `IndexDefect` fork as before. `--boundChecks:off`
  (`routineChecks` strips `coBound` as it does `coRange`; `RoutineChecks.boundOn`
  declines a `push boundChecks: on`): a bound-checks-off build no longer declines
  every routine, the in-bounds witness is exact and trusted, the out-of-bounds side
  is an `UndefinedFinding` (site; arrays carry the source line, a string expression
  read does not). The opaque-call scan answers the kind for an index in a scanned
  body under either option. Native: arrays by `-fsanitize=bounds` (a global or local
  array object; a PARAMETER array decays to a pointer and is invisible to it),
  seq/openArray/string by `-fsanitize=address` over `-d:useMalloc` (Nim's own arena is
  invisible to ASan; index `len` and `len + 1` trip, a negative index reads the block
  header and does not); probe `ubsan_support.indexProbeSrc`. Pins:
  `tsymex_0016_rangeoff` (updated), `tsymex_0016_boundoff` (new, `--boundChecks:off`
  cfg; RED shown by forcing `boundsUnchecked()` false: the seven halt tests fail).
  Known imprecision: a string `s[len]` is halted although C reads the NUL terminator.
  PRC-07 object and field halves (same branch, walker 306 kept, unreleased; RED shown
  first for each file): `--objChecks:off` removes `isObjDisplayCheck`, so `Der(b)` on
  a `Base` succeeds and reads another object's bytes: `UbKind` `ubInvalidObjConversion`
  (row `conv/objDowncast`, appended after `ubArrayOutOfBounds`), a new IR statement
  `isUndefined` the parser puts where it raised `ObjectConversionDefect`
  (`dsl_parser.nim` objConv arm), halted through `decideUndefined`; the subtype side
  and nil are exact; native pin ASan over `-d:useMalloc` (`ubsan_support.objProbeSrc`,
  derived type larger than the object), Windows skip. `--fieldChecks:off` makes `v.b`
  a plain union member access. cpp backend: `ubInactiveVariantField` (row
  `field/inactiveBranch`) halts a wrong-branch read, and a write too (C++ defines the
  assignment but the walker cannot hold a branch whose active member is not its
  discriminator's: halting is the sound omission); no native pin (no sanitizer sees it,
  gcc defines it as punning). c backend DECISION: the walker has no faithful per-target
  variant layout (no sizeof/offsetOf/byte-level machinery outside the host `sizeof/host`
  refusal; `heapLeafTerm` pinForm is a heap-array leaf form, not a C layout), so the
  wrong-branch side is declined on its own path (`feUnsupportedOp`, reason
  `fieldChecksOffLayout`, row `field/inactiveBytes`, a refused row), never a routine
  taint; the right-branch side is exact. REMAINING PRECISION ITEM: model the c
  backend's overlapping-bytes read exactly, which needs the C layout of a variant
  (arm struct offsets and widths per target, the discriminator's width and padding) and
  a bit-level reinterpretation of the active arm's slots (C11 6.5.2.3 note 95), pinned
  natively by value. A branch-changing discriminator write uses `dwmHavoc`
  (`discWriteMode`: `feUncheckedDiscBytes`, replay-confirmed) for a value variant and a
  path-local decline through a `ref` (`runtime_heap.nim` disc write); an infeasible
  havoc/decline outcome is no longer recorded (`x.k = ka` of a `ka` stays exact). The
  opaque-call scan answers the cpp kind for a `CheckedFieldExpr` and nothing on c.
  Builds: `objChecks=off`, `fieldChecks=off` cells; `routineChecks` strips `coObj` and
  `coField` in such a build (`objOn`/`fieldOn`; a push back on declines). Pins:
  `tsymex_0016_objoff`, `tsymex_0016_fieldoff` (both backends). PRC-07 stays open:
  the c-backend decline, nil checks, float checks (PRC-08).
  PRC-07 fieldoff follow-up (`rfc-0016-rangeoff`, walker 306 kept; RED first:
  `[FAILED] a write outside its branch is no finding on either backend` and the
  ref twin, on cpp): a cpp WRITE to an inactive union member is defined (it makes
  the member active), so it is no longer `ubInactiveVariantField`; it is declined
  path-locally (`fieldChecksOffLayout`, row `field/inactiveBytes`), as on c.
  `IRStmt.vfWrite` (identity only, set by the assignment parser on the write's
  own branch check) selects it; the heap write site passes `isWrite`.
  PRC-07 c-backend variant bytes, slice A (same branch, walker 306 kept; RED first:
  `[FAILED] the walker's variant layout is the compiler's`, then, with the layout
  in, `[FAILED] a wrong-branch read is the active arm's bytes, by value` and the
  five twins): DONE. The per-arm `SymVal` slots stay the representation; the union
  bytes are derived from them through a C layout per target.
  `smt/variant_layout.nim` computes it for a single-axis variant (struct
  `{plain fields; disc; union{one-field arm: the field; else struct _k_N}}`, read
  from the generated C; the C ABI places each member; amd64/arm64, little-endian,
  64-bit pointers, every other target declines with the reason) and pins each
  arm field's byte offset/width against `addr v.f` and `sizeof` natively
  (`Wd`, `Wp` with a plain field, `Wb` with a bool disc, `Wf` with a float arm).
  Consumer: on `--fieldChecks:off` c, `isVariantField` (value variant) answers a
  wrong-branch READ whose bytes lie wholly inside the active arm's integer, char
  or bool fields by `armBytesRead` (bv lshr/and/shl/or over the slots' 64-bit
  cells), and `lowerVariantFieldSet` makes a wrong-branch WRITE a bit-insert into
  those slots (`armBytesWrite`), the discriminator unchanged; per arm, so a
  symbolic discriminator splits into exact arms and a declined remainder
  (`fieldChecksOffLayout`, path-local). Needs `vfVariantTy`/`vfsVariantTy` on the
  IR (identity only, emitted by the parser). Declined, as before: uncovered
  bytes or padding, a float, a range or enum written with arbitrary bytes, a bool
  read of non-bool bytes, a bool field overwritten by a non-bool, the `else` arm,
  a multi-axis variant, a `ref` variant (one heap array per tag: not local), an
  inheritance variant, a `packed` object (invisible to the layout: unpinned
  trap). cpp: a read stays `ubInactiveVariantField`, a write declined.
  PRC-07 slice B (same branch, walker 306 kept, comment extended; RED first:
  `[FAILED] the walker's variant layout is the compiler's` with `walker
  size=16;x@8;a@8;b@12 native size=10;x@2;a@2;b@3` for a `{.packed.}` variant,
  then `[FAILED] a packed variant reads the active arm's bytes at its own
  offsets`, `bytes no field of the active arm owns are the zero of
  initialisation`, `a float arm is its IEEE bits, and int bytes read back as a
  float`, `an enum arm field is its raw C value`, `an int read past the active
  arm's fields takes the zero tail byte`; `tsymex_r6_r6_emit_roundtrip` RED
  `Error: not all cases are covered; missing: {isUndefined}`): 0a `{.packed.}`
  is alignment 1 at every level (`IRType.vLayoutPragma`, identity only, read by
  `dsl_typebridge.layoutPragmaOf` from the type's and its fields' pragmas; any
  other layout pragma declines the layout). FINDING: slice A's "unpinned trap"
  was never reachable: the walker declines every `{.packed.}` type at its
  construction (row `pragma:type/packed`, layout AND passing), so a packed
  variant's symex read is `sxUnknown` there (pinned so in the file); the
  layout is ready for the day that row is lifted. 0b the round-trip emitter covers
  `isUndefined`. Slice B proper: the per-arm slots stay the representation of
  the active arm; on c a value variant also carries the union as one byte image
  (`SymVal.vImage`, a 64-bit cell per 8 bytes, little-endian, built only under
  `unionImageGate`: `--fieldChecks:off`, c, layout derived), coherent by
  construction -- a constructor writes the arm's fields over zero
  (`lowerVariantLit`, the runtime-discriminator constructor, `defaultZero`), a
  free parameter over fresh cells (`allocateSym`, `variantImage` ite over the
  discriminator), `lowerVariantFieldSet` inserts every write into the image
  and re-derives the active arm's fields the bytes cover (`bitsPlace`), and
  `isVariantField`'s out-of-arm read extracts the target's bytes (`imgRead`)
  whichever arm is active (one path, no per-arm split); a write's out-of-arm
  side is exact in the arms it leaves with a value in every field
  (`writeExactArm`), the rest declined. Floats go through `toIeeeBv`/
  `bvToFpBits`, enums are their raw value (`PlaceKind.pkEnum`), a bool or
  `range` target of foreign bytes declines (`bitsPlace` none), `joinSV` merges
  images cell by cell, a branch-changing discriminator write drops the image
  (the new arm's slots are the havoc; an out-of-arm read after it declines).
  cpp: `SymVal.vActive` (the arm last written; constructors set it to the
  discriminator) replaces the discriminator in `isVariantField`'s arm
  conditions, a write is exact and sets it (`lowerVariantFieldSet`), a
  discriminator write leaves it, so `x.b = 5; x.a` halts
  `ubInactiveVariantField` and `x.b = 5; x.b` is exact. Slice A's
  `armBytesRead`/`armBytesWrite`/`pieces` are deleted. `field/inactiveBytes`
  keeps what the handoff's migration note lists. REMAINING: ref variants (the
  image as heap cells beside the per-tag arrays; `runtime_heap.nim` sites
  4270/5012 still decline), deriving the new arm from the image at a
  discriminator write (would replace `dwmHavoc` on c), a `range` target's
  raw value under `--rangeChecks:off`.
  PRC-07 hooks gate (same branch, walker 309 kept, comment extended):
  `IRType.vNoCopyMem` (`not supportsCopyMem(T)`, emitted by `emitIRType` as
  `symexNoCopyMem[T]()` so the compiler answers; a generic type is taken to
  have hooks) gates `unionImageGate`, so a hooked variant keeps `dwmHavoc`;
  it is in `==` and the canonical key. RED first: `tsymex_0016_fieldhooks` on c,
  `[FAILED] a variant with a user copy hook is the havoc model, never exact`.
  Note a user `=destroy` on a variant is a compile error with a discriminator
  assignment, and the layout already declines any non-scalar field, so the
  copy/sink hook is the reachable case. Remaining for `field/inactiveBytes`
  as listed in the migration note (bool/range targets, layout pragmas,
  `else`, multi-axis, an out-of-branch field write through a `ref` on c).
  PRC-07 slice B continued (same branch, walker 306 kept, comment extended; RED
  first, `tsymex_0016_fieldoff` on c: `[FAILED] a branch-changing discriminator
  write keeps the bytes: the new arm reads the old` (`pinExact ... sxUnknown;
  errors: feUncheckedDiscBytes`), `... to a narrower arm reads the first byte`,
  `a write into the new arm lands beside the carried bytes`, `a symbolic
  discriminator write carries the bytes too`; the range half, new
  `tsymex_0016_fieldrangeoff` (both `--fieldChecks:off` and `--rangeChecks:off`)
  RED on the previous sha: `[FAILED] a wrong-branch read of a range field returns
  the raw bytes`, `a range field overwritten with foreign bytes reads them
  back`, `a discriminator write into the range arm carries the raw bytes`):
  (3) DONE: `discWriteOutcomes` takes the variant type (`IRStmt.vrVariantTy`/
  `vrsVariantTy`, identity only, set by the parser) and the receiver's image; on c
  with the layout derived a branch-changing write keeps the image and the new
  arm's fields are `bitsPlace (imgRead image field)` (`DiscOutcome.keepImage`),
  no `feUncheckedDiscBytes`; a field the bytes are no value of (a bool, a range
  with checks on) falls back to `dwmHavoc`. Confirmed from the generated C and a
  native run (debug, ORC, release): `x.k = kb` is `x.k = 1` alone, the bytes
  stay. cpp keeps the havoc. Residual: a user `=destroy` hook on the variant
  object itself would zero it and cannot be read by a macro; the old havoc
  tainted for that, the c image path does not. (4) DONE: under `rangeChecks:off`
  `bitsPlace` returns the raw value for a `range` (`rangeUnchecked`) and
  `writeExactArm` accepts a range overlap; with its checks on it stays declined.
  (2) DONE in PRC-07 ref variants, below. Was: ref variants: the per-(tag, field) heap arrays are written at
  every ref constructor, field store, discriminator store and `new`; an image
  heap beside them must be coherent at all of those and at an input ref's first
  materialisation (the image cell of an address must equal the pack of the
  active arm's cells), which is more than the two decline sites
  (`runtime_heap.nim` read and write `fieldsUnchecked` arms) the brief named.
  FIXED (PRC-07 zero-fill, walker 309 kept): the image's "zero of
  initialisation" holds only for a default-initialised `var x: V`,
  `default(V)`, a constructor omitting a field and a `result` set field by field
  (generated C `nimZeroMem`). A constructor naming every field
  (`V(k: ka, a: v)`) is `x.k = 0; x.a = v` with no zeroing, so the bytes no
  field of the active arm owns are unwritten. The union image now carries an
  indeterminate-byte mask beside the data (`imgWrite` clears it over what it
  writes; `x = V(...)` over an existing variable keeps the old image's bytes);
  `IRExpr.vlZeroFilled` (parser, in the cache key) says which constructions
  zero; `imgReadDef` reads `ite(mask == 0, data, U)` with `U` a fresh
  unwritten leaf, and `isVariantField` taints the path (`forkPathTainted`,
  `ubIndeterminateRead`) when a read observes one; `retBindEq` ties the
  returned image's cells. Verdict: `sxSat` untrusted with the kind when the
  replay confirms, `sxUnknown` + `feGlobalHavoc` when it refutes (the callee-built
  case: the callee's garbage is its own stack), the `{.noinit.}` convention, not
  a new behaviour. Pins `sutPadRead`/`sutPadZero`/`sutPartialRead`/
  `sutIntFromBytes` re-pinned to it (`indeterminateOrRefuted`); the zeroed
  constructions stay exact.
  REMAINING, slice B: uncovered bytes/padding and the cpp "active member
  differs from the discriminator" state (write then read through the
  discriminator's branch is UB), which need a union byte image on the value
  (a new `SymVal` field merged by `iteSV`, `svPartsOf`, retBindEq, hashing: ~100
  sites).
  PRC-07 ref variants (same branch, walker 309 kept, comment extended; RED
  first on 708589c8, new `tsymex_0016_fieldref` (`--fieldChecks:off`): c
  `[FAILED] a branch-changing discriminator write through a ref reinterprets
  the bytes`, `through an alias`, `a constructor naming every arm field leaves
  the other arm's tail indeterminate`, `new zeroes the cell: the other arm's
  tail is zero`, `an input ref's bytes are free`; cpp `[FAILED] a read through
  the member the wrong-branch write made active`, `a read through the
  discriminator's branch after a wrong-branch write`, `a branch-changing
  discriminator write leaves the old member active`): a heap case object
  carries the union image in `<id>__@img<i>`/`<id>__@msk<i>` heaps
  (`runtime_heap.nim` `cellImage`): the active arm's bytes are packed from its
  field heaps at every read, so every writer of an active field (field store,
  pointer into a field, havoc) and an input ref's first read are coherent by
  construction; the stored heaps are written by `isNew` (zero for `new`, all
  indeterminate for `isNew.nUninit`, a constructor naming every field of its
  arm: generated C `nimNewObjUninit` vs `nimNewObj`, c and cpp, debug and
  release), `variantCellStore` (a whole store, an address cell) and a
  branch-changing discriminator store (fixes the old arm's bytes, then reads
  the new arm's fields from them). cpp: `<id>__@act`/`<id>__@acton` hold the
  active member (untouched: the discriminator's arm); a field write makes its
  arm active, a discriminator store fixes the old one, a read through another
  arm halts `ubInactiveVariantField`. `symexNoCopyMem` asks `supportsCopyMem`
  of a `ref`/`ptr` symbol's pointee (it answered `false` for every `ref
  object`). An out-of-branch field write through a `ref` on c is exact (`outOfArmFieldStore`,
  runtime_heap.nim: the field's bytes into the stored image heaps at its layout
  offset, the mask cleared, every covered field of the arms `writeExactArm`
  accepts re-read from the image; a bool, a checked `range` or the `else` arm
  keeps the value path's per-side decline); `havocOpaqueHeaps` gives an opaque
  call's havoc the zero mask array (the convention of a value variant's
  `allocateSym` and a rebound `{.noinit.}` local; the path is already tainted
  `feOpaqueEffectHavoc`), so a byte the constructor wrote is no longer a
  spurious `ubIndeterminateRead` after the call (cost: a byte the callee never
  wrote and the ctor left indeterminate also reads determinate there, replayed
  not halted). RED then GREEN on `tsymex_0016_fieldref` (c): `[FAILED] an
  out-of-arm write is read back through the active arm's field`, `... whole
  through the same field`, `... keeps the bytes it does not cover` (sxUnknown,
  `fieldChecksOffLayout`), `a ref variant fully written by its constructor stays
  determinate over an opaque call` (`ubIndeterminateRead`). The stale
  `tsymex_0016_fieldoff` ref pins are re-pinned to the new model. Remainder: an
  `else` arm is neither imaged nor tracked.
  K10a-axis (`rfc-0016-k10aa` on `rfc-0016-k10at`, walker 299 to 300 in int4b, was 293 to 294;
  at landing): `smt/definedness.nim`, an `AxisTable` keyed `<op>/<class>`
  (`ArithOp` x `OperandClass`, `noalias` among the classes) answering by
  `DefProfile` (checked, unchecked, fwrapv): defined / Defect / undefined with
  a `UbKind`. Read by `lowerArith`/`depositSignedOverflow` (the overflow,
  zero-divisor and `low(T) by -1` rows, same answers as the hand-written
  traps), `unwrittenUb` (`read/uninitialised`), the ref/ptr ordering arm
  (`order/pointer`, STY-03 `never`), the stale element pointer marker
  (`grow/elemAddr`, STY-07 `never`) and `withCheckDeclines` (`call/noalias`: a
  `{.noalias.}` parameter beside another pointer-like one declines; new). The
  other 14 arithmetic cells are allowlisted to K10c (`tests/0016-allowlist/
  defined.txt`). `ubFloatToIntRange` is REMOVED from `UbKind` (no producer):
  K10a-float re-adds it, at the END of the range (after `ubSignedDivZero`),
  with its halt site and a row (codec 4 is unreleased, so the ordinal shift
  here needs no meta bump). `pinUndefined` (`s8cu_helpers`) evidences a kind that rides a witness instead of halting.
  K10c (`rfc-0016-k10c` on `rfc-0016-k10aa`, no walker change; 300 on int4b):
  `tests/tsymex_0016_k10c_ubsan.nim` (+ `.nim.cfg` `--overflowChecks:off`, the
  `dpUnchecked` profile) pins the 14 arithmetic `defined:` cells twice, tied by
  the table: the walker through `symexFind` (`pinDecline` with the row's `ub`,
  or `pinExact` for the defined narrow rows) and C through
  `tests/ubsan_support.nim`, a child built once with `-fsanitize=undefined
  -fno-sanitize-recover=all` that runs one `(type, op, a, b)` per process.
  Each case's expectation is derived from `definedness(op, class, profile)`
  and an operand oracle that does not use C (`pinUbsanCell`, a `pvCrashed`
  record, entry `pinUbsan`, never evidence by itself). A second child adds
  `-fwrapv` (`dpFwrapv`; `low(T) div -1` may end in SIGFPE there). The
  14 `defined.txt` lines are gone (the walker pins evidence them on every
  leg). `tests/tsymex_0016_k10c_fma.nim`: the walker's unfused `a*b+c` hits
  natively, a `-ffp-contract=off` child equals the default child, a `-mfma`
  child (CPU permitting) computes the fused bits. New build cells
  `cflags/sanitize` and `cflags/fpContract` (`never(unobservable)`); the
  Windows rows are allowlisted `rows=` with a reason, UBSan parts are
  `skipCell`. `CFlag` gains `cfFpContract`, `cfNoStrictAliasing`;
  `assumedAbsentNote` is appended to every `haltUndefined` message and the
  flags are tabulated in `docs/symex/README.md`. Trap: `-O0` gcc never
  contracts, so the FMA probe builds at `-O2`.
  K10c float cell (int4b follow-up): `defined:convert/floatToInt` joins the UBSan
  pins through a second probe built with `-fsanitize=float-cast-overflow` (not part of
  `-fsanitize=undefined` in gcc); NaN, an infinity and a value outside int64 trip, in-range
  values (truncation included) run clean; mingw/MSVC declare it with `skipCell`.
  Precision (int4b, walker 300, K10a-float's semantics): the float -> int row is keyed
  by the C lowering Nim 2.2.10 emits (generated C read at -O0/danger/default, UBSan at
  the boundaries in `tsymex_0016_k10c_ubsan`). `definedness.floatToIntLowering(src, tgt,
  signed)` is the table:
  | target | float64 operand | float32 operand | row |
  |---|---|---|---|
  | int64, int | `(NI64)f` direct | direct | `convert/floatToInt` |
  | int32 | `(NI32)((NI64)f)` | `(NI32)f` direct | `Via` / direct |
  | int16, int8 | `(NI16)((NI64)f)` | `(NI16)((NI32)f)` | `convert/floatToIntVia` |
  | uint8/16/32/64, uint | `(NU8)f` direct (negative or >= 2^w is UB) | direct | `convert/floatToInt` |
  A distinct int takes its base's lowering. Undefined iff NaN, an infinity or the
  truncation is outside the INTERMEDIATE; inside it the narrowing is the C integer
  conversion, modulo 2^n (gcc documents it, implementation-defined; the same assumption
  the 8/16 bit arithmetic rows already make, so no new `CFlag`), and the walker models it
  exactly (`int8(300.0) == 44`, trusted). The `range` target check (`Natural(f)`) still
  tests the converted value. Restored: `tsymex_rfc0005_s8g_models` `int8(f)` wrap (sxSat,
  replay); the other K10a-float rewrites are NaN/inf or `int`-target driven and stay
  `sxUnknown`. New cell `defined:convert/floatToIntVia` (evidenced by `pinDecline` in
  `tsymex_0016_k10af_float`, UBSan-pinned in k10c).
  K10a-float (`rfc-0016-k10af` on `rfc-0016-k10aa`, walker 300 (shared with K10a-axis), its
  comment extended): `ubFloatToIntRange` is back at the
  END of `UbKind` (ordinal after `ubSignedDivZero`; `static` pin extended).
  Row `convert/floatToInt` (`ArithOp.aoConvert`, `OperandClass.ocFloatToInt`,
  site `dsConvert`) answers undefined under every profile: Nim 2.2.10 emits a
  plain C cast and range-checks the cast value, so no check profile raises.
  Consumer: `drainConvFloatToIntFresh` (`runtime.nim`) reads
  `convertDefinedness(defProfile())` and decides the out-of-domain side as
  `drainArithTraps` does (provably unreachable: `logPrune`; else
  `haltUndefined`); the in-range continuation carries the domain in `pc`
  (it was `defectSurvivorPc`). The tainted fresh-value fork is gone, so
  `feConvFloatToIntUndefined` has no producer (still allowlisted to K9c, W-64
  deletes it). Precision change: `int(NaN) == low(int)` is no longer a
  reachable label (the halt does not claim a platform value); it is a
  `tUndefined` finding. A `range` target (`Natural(f)`) still raises through
  `rangeDefectConds`. Every undefined finding names its own source site:
  the float -> int conversion carries `IRExpr.convSite` and the signed
  `+ - * div mod` binop `bsite` (`file:line:col` from the parser, part of
  the canonical key when set), `convFloatToIntBoundConds` holds `ConvBound`
  (cond + site), and `lowerArith` takes the op's site as a parameter so the
  arithmetic traps name their op ("signed ... overflow at file:l:c"); two
  conversions or ops in one SUT are two findings. Every binop the parser
  rebuilds (`+=`-style compound assignment, `inc`/`dec`, `succ`/`pred`)
  takes the site of its source node (`siteBinop`).
  Pins: `tests/tsymex_0016_k10af_float.nim`, `tsymex_0016_k10af_sites.nim`,
  `tsymex_0016_k10af_sites_checksoff.nim`.
  K10a-float sites (int4b follow-up, walker 300): a signed negation (`iekUnop.usite`) and
  the borrowed operators (`iekBorrowOp.borrowSite`) carry their source node's
  `file:line:col` like the binops (`withSite`), read by `lowerArith`; two negations (or two
  borrowed `+`) in one SUT under checks off are two findings. Pins: `tsymex_0016_k10af_sites_checksoff`.
  K10a-concolic (`rfc-0016-k10ac` on `rfc-0016-k10aa`, walker 300,
  comment extended): `drainArithTraps` records each `ub` deposit of a
  `wmFollowConcrete` replay (`ConcolicDefinedFact`, stamped with the decision
  count); `runConcolicFlipImpl` conjoins the facts with `at <= target` into
  EVERY attempt (the prefix already carried them, but the optimistic
  relaxation drops conjuncts last-first and so used to hand back
  `b == 0` / an overflowing pair as a seed), and solves the other disjunct for
  the target condition's own operations: `ConcolicFlipResult.undefinedReached`
  (kind, site, input; never a seed; counter `flipCounters.undefinedReached`,
  folded). The prefix handed to that query drops the op's own defined side
  (the walk had put it in `pc`). Checked-build signed `div`/`mod` by zero and
  overflow stay Defect forks (raise), not UB, so they are not
  facts. Pins: `tsymex_0016_k10ac_concolic{,_checksoff}`.
  Reader (same slice): `tryConcolicBridge` folds each flip's
  `undefinedReached` into the orchestrator (deduplicated per (kind, site),
  first witness kept) the way `annotationViolations` is, and
  `FuzzReport.undefinedFindings` hands them to the caller;
  `formatUndefinedFindings(report)` is the human summary. Pin:
  `tfuzzconcolicundefined` (registered in `nelli.nimble`; a `fuzzConcolic`
  campaign over `a div b > a` with `b == 0` at one magic draw).
  K10b (`rfc-0016-k10b` on `rfc-0016-int4b`, walker 300->301, a *round*):
  whole-run definedness (section 9.1 item 3). `SymexSettings.wholeRunDefinedness`
  (default `true`, in the cache key through `canonicalize`): a clean label
  `sxSat` is checked by a second walk (`verifyTailDefined`, `runtime.nim`) from
  the entry in `wmFollowConcrete` under the witness's model pins
  (`RawWitness.pins`: `leaf == model(leaf)` over `svLeafTerms` of every param,
  built in `trySolve` while the model is live; an unpinnable leaf stays free,
  which only widens the check), with a sentinel label so `shouldStop` never
  fires, to the routine's exits. Every `UbKind` a halt records on a side the
  pins do not rule out (`haltUndefined`'s `concretelyInfeasible` test) joins
  `Soundness.witnessUndefined`; a decline, a budget, `walkWorkExhausted` before
  or after the walk, or a lossy witness (`gateLossyWinner` in `symex.nim`,
  before replay) adds the new `ubTailUnverified` (appended to `UbKind`,
  ordinal 6, `classOf` `dcOmitted`). `trustedSat` needs the set empty and
  replay cannot lift it. The explore walk is untouched: the gate only moves
  trust. `scanOpaqueDefects` is parameterised (`IRStmt.opaqueUndefined`,
  emitted through `ubMaskOf`/`ubSetOf`, canonical key `;undef=`): a foreign or
  unreadable body (closure, method, re-raise, too deep) answers
  `ubTailUnverified` through the new definedness-axis row `call/opaqueBody`
  (`ocOpaqueBody`, `dsOpaque`, `opaqueBodyDefinedness`); float-source
  conversions answer the `convert/floatToInt` row; overflow and division
  magics read the owner's check options (`ownerChecksOn`) and answer
  `ubSignedOverflow` / `ubSignedDivZero` / `ubIntMinModMinusOne` when the owner
  is unchecked, `ubUnsignedDivZero` for `DivU`/`ModU` always (W1-d1b's open
  end). On the second walk `opaqueRaiseForks` (under `WalkCtx.tailGate`, which
  the concolic collect driver never sets) ends every path that concretely
  reaches such a call. Pins: `tests/tsymex_0016_k10b_round.nim` (+ `.nim.cfg`
  `--overflowChecks:off`, the `dpUnchecked` route; a `{.push.}` is W1-d2's
  decline): (a) overflow after the label untrusted with `ubSignedOverflow`
  (`pinUndefined` on `add/signedWide`), (b) the same op on a branch the witness
  does not take trusted (`pinExact`), (c) a foreign call after the label
  untrusted (`pinUndefined` on `call/opaqueBody`), (d) a lossy shape
  (`rendersAsDefaultObject`) untrusted, (e) gate off is 0.9.2's verdict,
  (f) `symexFindAllWitnesses` trusts per finding. Forks resolved by
  recommendation: gate default ON (a round is for flipping trust; the key
  carries it); ONE new kind for every fail-closed answer rather than one per
  cause (the cause is in the message; a kind per cause would widen `UbKind` for
  no reader); the opaque "may be undefined" answer is a table row, not a
  hardcoded kind, so the universe ledger evidences it; a lossy witness fails
  closed as the RFC says even though the model pins could follow it (the
  precision follow-up below closed that). The 0.9.2 known gap is closed in the RFC, the
  migration note and CHANGELOG. Perf reading (K10 SUT set, gate on vs off, two
  lanes side by side so wall time is indicative): explore units are identical
  on and off in every file (the explore walk is untouched); the tail walks'
  own units (`k10b-tail` lines of `NELLI_WALK_UNITS_LOG`) per file, explore ->
  tail: k10aa_axis 4815 -> 12348, k10af_float 215072 -> 24553, k10af_sites
  211776 -> 7537, k10af_sites_checksoff 78319 -> 39013, k10at_target 1549055 ->
  532, k10b_round 7389 -> 499300 (the outlier: follow-mode halts under pins on
  wide int64 overflow sides; a precision/perf follow-up), k10c_fma 75314 ->
  2026, k10c_ubsan 88278 -> 550, the concolic pair 0 (no label walks). Wall
  time of the whole dt-bounded run (compile included), on vs off, seconds:
  axis 72/53, concolic 49/53, concolic_checksoff 80/57, float 64/61, sites
  70/50, sites_checksoff 57/55, target 90/64, k10b 55/55, fma 76/68, ubsan
  72/47; every gate-on run green (rc 0, 0 failures); under `-d:nelliGateOff`
  only `k10b_round`'s four trust tests fail, as they must. Not run before the
  handoff (context line reached): the rest of the final batch
  (`tfuzzconcolicundefined`, `tsymex_0016_w1d*`, `CR2_cachekey`, `k2a_census`,
  `N2_kindgate_audit`, `s8ab_letaudit`, `s1_lattice`, the five
  `scanOpaqueDefects`/`mkOpaqueCall` consumers `k4a_guard`, `163rev_inert_argfork`,
  `g3fix_walkergap`, `r6_r6_emit_roundtrip`, `rfc0005_w3_opqchecks`, and
  `tsymex_0016_universe` with the ledger regen); the script is
  `scratchpad/k10b/batch.sh`. `check-readme-kinds.sh` and `check-worklist.sh
  check` pass. No worklist TOML row is owned by K10b (the W1-d1b hand row
  carries the note).
  K10b follow-up (2026-11-09, same walker 301, after the rebase onto int4b
  `82028e37`): (i) a lossy winner is tail-checked like any other
  (`gateLossyWinner` fails closed only when `RawWitness.pinsComplete` is false:
  `modelPins` skipped a parameter or leaf), so a lossy-witness SUT with a
  defined tail is `trusted()` (test (d); (d2) an undefined tail untrusts it by
  its own kind); RFC section 9.1 item 3 reworded to "cannot be followed" being
  the condition. No shape in the corpus reaches the incomplete-pin branch
  (object, variant, seq, Table, set, array, ref params all pin completely), so
  it is a defensive guard with no pin of its own. (ii) The `k10b_round`
  outlier (7389 explore units -> 499300 tail units) was the pins, not the
  overflow sides: `svLeafTerms` returned the heap leaf of a signed int field as
  its Int projection (`ite(bvslt b 0, ubv_to_int b - 2^64, ubv_to_int b)`), so
  `leaf == model` made every query of the second walk mixed-theory over 64-bit
  words; a tail with nothing in it cost 477,838 units. `svLeafTerms`/
  `heapLeafTerm` take `pinForm`, which returns the value's own bit-vector, so
  the pin folds. The halt also no longer lists a finding under `tailGate`
  (`listIt`), which solved an unpinned witness query nothing read. Before ->
  after tail units: lossy stub with a defined tail 477,838 -> 126, with an
  overflow 956,056 -> 518, scalar overflow 7,038 -> 3,648, scalar branch 126 ->
  126, foreign call 48 -> 48; pin (g) bounds a defined object-param tail under
  20,000. Also fixed in the rebase/batch: the scan's float conversion reads
  `convertDefinedness(ocFloatToInt, dpChecked)` (int4b gave it a class
  argument; both float rows answer one kind), `tsymex_configdefaults` (field
  count 9, merge carries `wholeRunDefinedness`), `tsymex_rfc0005_s6a_budget`
  (the K7 walk-cap `beBudgetExhaustedPrune` site was never counted),
  `tsymex_0016_w1d3_undefined` (mask 64 is `ubTailUnverified`, valid; 128 is
  the first invalid), universe ledger regenerated for `call/opaqueBody`.
  K10b fail-closed fix (`rfc-0016-k10fix`, walker stays 302): a tail branch
  still undecided after `followBranchOutcome`'s retry under the path's `pc`
  walked on without either arm, so an undefined op in an arm was skipped and
  the `sxSat` stayed trusted (RFC 9.1 item 3: an undecided side counts as
  undefined). `WalkCtx.tailUndecided` now fails the tail check with
  `ubTailUnverified`. Exception, the root of the `NewString`/`NewStringOfCap`/
  `SetLengthStr` regressions a blanket fail-closed caused: `setLen`'s
  shrink arm of a grow has a `pc` the pins contradict (both asks unsat), the
  replayed run is not on that path, so it does not count
  (`concretelyInfeasible`). Pin: k10b_round (i), a branch on an unwritten
  module global with a checks-off overflow arm. A ref-param SUT
  (`tsymex_rfc0005_s8n_precision`) also lost trust, since its `p != nil` and
  `p.v` were unpinned: `modelPins` now also pins each ref sort's `nil`
  constant (no completion) and every free `heap_*` array the model interprets,
  so those branches decide. Batch (k10b_round, k4a/k4b/k4c, k10*, g1b, g2,
  s8n_precision, tfuzzconcolicundefined, CR2, universe cmp identical): green.
  K10d (`rfc-0016-k10d` on `rfc-0016-k10b`, walker 301->302): `SymexSettings.arithChecks`
  and `SymexResult.fromCache` deleted (INT-39, INT-41 closed). The build is the
  only source of the check gates: `checked(ac)` (`runtime.nim`) reads
  `arithChecksFor()` plus the pushed-checked routine case, so the gated drains
  and the `acRange` narrowing fork follow the build, and a drain for a check
  the build lacks returns the path (the undefined side is the definedness
  axis's). `noteArithChecksDisagreement`, `effectiveArithChecks`,
  `arithChecksDisagree`, the merge line, the two `validateSymexSettings`
  warnings and the `arithChecks=` canonical key are gone (`ArithCheck` and
  `arithChecksFor` stay as the build gate). The cache number moved only for the
  key's shape (CR2 pin 302). Tests that used the setting as a lever were
  removed with it (R16-1 parts 4-7, the opt-out tests of R16-2/3/4, phase2
  overflow's signed opt-out, s8cu push/cl_over settings tests, 161's two
  unchecked-setting tests, w1d2's three settings tests, w1_parity WA-11,
  `phase14_c1_fromcache`); the rest read `arithChecksFor(buildSemantics)`.
  New: `tsymex_0016_k10d_removals` (RED: four `compiles` pins and the
  version floor; GREEN after). `docs/migration/0.10.0.md` written. TWO FACTS
  THE SLICE BRIEF GOT WRONG: the walk-units log has three columns on this
  base (the K10b tail walk adds `k10b-tail` lines, no fourth column), and the
  "`Admit`-taking IR constructors" (`mkMagicCall(a: Admit..)`) do not exist
  in code; the note says so rather than documenting them. The universe ledger
  is unchanged.
  ADM-IR (`rfc-0016-admir` on `rfc-0016-k10d`, no walker bump): the type x
  memory-op axis's node takes its proof: `mkZeroValue(zero: Admit[TypeOpModel];
  ty)` asserts an admitted `fieldDefault` row with `zmZeroValue`; the payload
  types moved to `types.nim` (typeaxes re-exports), `admitZeroValue(kind)` is
  the verb, the emitter re-asks it. Census: zero raw `iekZeroValue` builds
  outside `types.nim`. Test `tsymex_0016_admir`. ADM-IR remaining axes (walker 303): `mkOpaqueCall` takes an `OpaqueScan` (definedness and magic-defect rows, via `noteUndefined` / `noteMagicDefect`; `unscanned` for the three arms that never scan); `mkMathCall(Admit[StdlibBody]; ...)` with the parser declining a declined or absent float row at parse time (rows added for abs/min/max/isInf/isFinite/isNormal/toFloat32/toFloat64, nextafter declined; absent declines `feUnsupportedOpAborted`; this is why the walker bumps: such a program's IR carries a marker, not an `iekMathCall`); `mkArithBlock(ArithScopeProof; ...)` (pragma row, stdlib row, or the build); magics: `lowerMagic(proof, body)` wraps every `dispatchMagic` arm, census of `of "<magic>"` arms outside a dispatch is zero. Expression-form magic reads (walker 303, no change): `whenMagic` / `whenMagicIn` (`magic_rows.nim`) read the row at `msArm` and lower through `lowerMagic` for `IsNil`, the `repr` group (`BoolToStr`, `EnumToStr`, `IntToStr`, `Int64ToStr`), `Move`, `SetLengthSeqUninit`; `declinedMagic` carries `ProcCall`'s decline under its declined row; `magicIs` is the table-checked name compare (`Chr`, `Swap` in the analysis procs). Rows added: `IntToStr`, `Int64ToStr` (modelled, pinned in `tsymex_0016_k4b_cells`). Census `magicReadsOutsideDispatch` counted 8 before (the five plus `Chr` and the two `Swap` compares), 0 after, no allowlist. PCRE documented as enforced at its runtime consumer. K10b precision (walker 303->304, in the same branch): `modelPins` pins each ref sort's `nil` by model completion, so an explore-unmentioned `nil` no longer leaves a tail branch undecided. The RED named in the brief did not reproduce: in every shape tried (ref param unconstrained, two ref types, `seq`/object fields, `ptr`, empty `pc`) Z3's model already interprets `nil`, so the branch decided before the change; `tsymex_0016_k10b_round` (j) pins the decided, natively-agreeing behaviour and the 304 floor. A global ref stays `ubTailUnverified`. `docs/migration/0.10.0.md` updated.
  PRC-02 (`rfc-0016-prc02`, walker 309 to 310, with INT-13): a proc value now
  crosses a re-executed replay by identity. `replaywire.nim` writes it as the
  index of a routine in a table (`procs`) that both ends build from the
  program's own top-level routines the footprint scan read (the child is the
  same binary), so a global, a field or a hook holding one replays, and
  `scanFootprint` no longer opens on a proc-typed symbol or a call through one:
  a routine named in code it reads is scanned, and the wire writes no other. A
  closure with an environment, and a routine the code does not name, decline
  naming which. A `{.global.}` named by a routine nested in (or called by) the
  one that declares it is the child's own, as the declaring routine's use
  already was (`ownGlobals`, checked against the set of routines scanned). The
  six runtime hooks go through the same wire (`putHostHooks`/`readHostHooks`
  in `replayproc.nim`; the child keeps its own `outOfMemHook` and chains the
  host's), so a hook naming a routine the SUT names is reinstalled and any
  other still declines naming the hook; `setControlCHook` stays INT-15. A
  proc value naming a borrowed, magic or system routine declines: the table
  holds only routines with a body (`addressable`, after a Windows ICE on
  `cast[pointer]` of a borrowed `==`). A `method` declines (static,
  `refusedNotMarshallable`) naming the method, its base type and why: "`area`,
  a method on `Base`, whose overrides the scan cannot list (one may be declared
  in a module `<entry>` cannot see; a Linux or macOS run forks and replays
  it)". `procCall m(args)` around a method is a static call and scans `m` as a
  plain routine (the typed tree is `Command(Sym procCall, Call(Sym m, ...))`).
  Probes (Nim 2.2.10, orc, default dispatch; sources in the PRC-02 session
  scratchpad `method-probe/`): (3) the dispatcher is an `isObjDisplayCheck`
  if-chain generated into the main module's C after every module is semmed, and
  an override declared in a module the entry cannot see still runs (the test
  imports the SUT module, the SUT module imports the override module without
  exporting it); (4) two modules may declare the same-signature override and
  the dispatcher silently picks one (INT-48, an upstream Nim issue candidate).
  So no macro-time enumeration bounds the override set and the footprint must
  not assume a closed world; the walker's `methodRegistry` does (S8bn), and the
  replay is its safety net. Pinned in `tests/tsymex_0016_prc02_reexec.nim`
  (re-exec on Linux via its `.cfg`), including probe 3 through
  `tests/helpers/prc03_{types,over,sut}.nim`: the decline under re-exec,
  `roConfirmed` under fork. PRC-02 is closed; PRC-02b is the next slice:
  patch the in-house Nim's `cgmeth.generateMethodDispatchers` to emit a
  per-binary (base method, receiver RTTI, override address) table so the
  re-exec child can confirm dispatch soundly.
  PRC-02b (`rfc-0016-prc02b`, no walker bump: the footprint and the replay run
  change, the walk does not): toolchain patch 0008 (`patches/2.2.10/
  0008-method-dispatch-table.patch`, branch `prc02b` of the `toolchain` series)
  makes the main module's C of an executable (never `--app:lib` or
  `--app:staticlib`, whose symbol would collide when two Nim libraries link; the
  accessor is hidden) carry `void* nimMethodDispatchTable(NI* count)`, a
  static const table of {dispatcher address, method body address, receiver type
  name} rows in each dispatcher's if-chain order, and defines
  `nimHasMethodDispatchTable`. With it, `scanFootprint` no longer opens on a
  method: it scans the method and every override `methodRegistry` holds for the
  name, and `replayFootprint` hands `emitReplayWitness` the methods the code
  dispatches (a `procCall` is not one) and every method it scanned. The host,
  which is the child's binary (a library build keeps the stock decline: `hasMethodTable` in `replayproc.nim` is false there), calls `methodDispatchRefusal` (`replayproc.nim`)
  before it spawns: every row of the dispatchers' buckets must be a scanned
  body, else `refusedNotMarshallable` ("an override of `area` for `Sub` the
  entry could not see", not run-dependent). The table is the oracle for
  probes 3 and 4: it lists the override in the module the entry cannot see and
  the one of two same-signature overrides the compiler kept. The check is
  conservative: a whole bucket is checked, not the receivers the replay can
  build, so an unread override of an unrelated subtype also declines.
  `replayWitness` now registers the methods it needs (`methodPrelude`) as the
  other entries do. Stock Nim keeps the PRC-02 decline. Not done: the artifact
  is not published, so no CI leg has the define yet; `symexFind` over a method
  SUT stays `sxUnknown` through the route scan (`routeScan`, `feGlobalRoute
  Unproved`), which is compile-time and which the table cannot answer.
  PRC-07/08 remainder (`rfc-0016-prc0708`, walker 311): float checks are
  walked as compiled. `RoutineChecks.nanOn`/`infOn` (`check_options.nim`)
  mark a routine whose position has the option on at every reading; the
  parser stamps each float infix `+ - * /` with them (`IRExpr.bFloatChecks`,
  a compound assignment with the build's, as system's generic `+=`), and
  `lowerArith` deposits, in the generated C's order, `FloatInvalidOpDefect`
  on NaN, then `FloatOverflowDefect` on `+inf` / `FloatUnderflowDefect` on
  `-inf` (`depositFloatChecks`, drained as raises through `arithTrapConds`
  so one expression's checks stay ordered). The opaque scan also notes
  `FloatUnderflowDefect`. nilChecks closed as not applicable (no such option
  in 2.2.10; regression pin). Pin `tsymex_0016_floatchecks`. Remainder,
  same walker: the compound-assignment claim was probed natively (c, cpp):
  `x /= 0.0` in a routine pushed `nanChecks: on` runs on in a default build
  and raises in a `--nanChecks:on` build even under `push nanChecks: off`, so
  it takes the build's checks; a float `/=` is lowered now (it declined
  `feUnsupportedStmtKind`); pins in `tsymex_0016_floatchecks` and
  `tsymex_rfc0005_s8cu_cl_float`. PRC-08 closed: `tsymex_0016_danger`
  (`-d:danger --opt:none`) reads every option off through `buildSemantics`
  and `routineChecks`, and pins one SUT per kind (range exact, bound
  `ubArrayOutOfBounds`, field exact on c / `ubInactiveVariantField` on cpp,
  object `ubInvalidObjConversion`, `{.noinit.}` `ubIndeterminateRead`, float
  unchecked unless pushed). `math.ceilDiv` lowered by name (`parseCeilDiv`,
  row at the new `ssNameCall` site): its asserts are NOT compiled out. A
  generic's asserts follow `assertions` at the site that first instantiates
  it (native: `ceilDiv(-7, 3)` raises `AssertionDefect` in a debug module;
  under a first `push assertions: off` call every later call returns
  6148914691236517203), while its generated checks follow the definition's
  push (`floorDiv(low(int), -1)` SIGFPEs). So it is exact inside the
  precondition and a path outside it (`y == 0` included) declines
  `feCheckOption` naming the cell. The `pragma.txt` entries for
  `routine/nanChecks`, `infChecks`, `floatChecks` are removed (pinned exact).
  W3-z R1 (`rfc-0016-w3z-runtime`, walker 311 to 312, finding U3):
  `tUndefined` hits the `{.noinit.}` read. The read rides the path as `ub` on a
  `feGlobalHavoc` degrade and never halts, so `haltUndefined`, the only hit
  test, missed it and `symexFind(f, tUndefined())` was a trusted `sxUnsat`.
  `noteUbAtFork` (beside `haltUndefined`) is called from `forkPathTainted` and
  `taintInPlace` for each kind a degrade newly puts on a path, and solves the
  hit under `stkUndefined`; its taint is the parent's, so the carrying degrade
  does not demote the finding to a replay-only candidate. `ubTailUnverified` is
  out of `allUbKinds` (the default) and `tUndefined` refuses it (`doAssert`; a
  compile error for a static call). Pins: `tsymex_0016_w3z_r1_noinit_target`.
  Open: a read inside an `and`/`or` operand is lowered unguarded
  (`shortCircuitPartIsPure` sees no hoist and no inline fork), so
  `tUndefined` reports it reachable when only the other operand guards it.
  W3-z R2 (`rfc-0016-w3z-runtime2`, walker 312 to 313, finding U1): a
  replay-confirmed candidate is held to the whole-run gate. Its tail was
  never walked, so `symexFind` of a label on a havoc-tainted path followed by
  a signed overflow was `sxSat`, `rsConfirmed`, `trusted()`. `runSymexImpl`'s
  `sxUnknown` branch now walks each `sxSat` label candidate's tail
  (`verifyTailDefined`, gate and replay on) while its model pins are live,
  and the kinds join the existing `SatCandidate.witnessUndefined`, which
  `settleCandidate` already carries and the soundness codec already stores
  (no new field). The walk runs with `overApprox`
  (`WalkCtx.tailOverApprox`): a candidate's path carries a fresh symbol the
  pins do not fix, so a branch the pins and `pc` leave open forks both arms
  (`walkIfFollowConcrete`, `walkWhileFollowConcrete`) instead of setting
  `tailUndecided`, and a `dcFreshSymbol` record is not a reason for
  `ubTailUnverified`. Without that, every candidate would answer
  `ubTailUnverified` and none would be trusted. Pins:
  `tsymex_0016_w3z_r2_candtail`. Open: the winner's tail walk keeps the
  strict mode, so a post-label havoc on a clean winner is still
  `ubTailUnverified` (precision only). An opaque call's result is
  `feOpaqueCallUnmodelled` (⊤), never a candidate, so only havoc-tainted
  candidates reach this path.
||||||| 32ae1cf0
- **W3-z E2 (`rfc-0016-w3z-evidence2`):** the join evidences a UB-modelled `defined:` row by a public-entry record reporting its UB kind; the 23 E1 allowlist entries are cleared (the GCref table kind is now `feUnsupportedExprKind`, because the `GCref` magic exists only under the refused `--mm:refc`; `Repr` is declined, since repr(bool) and repr(enum) are the BoolToStr/EnumToStr rows; exact pins added for the cstring/pointer/proc by-value formals and the letCursor rows). Per-axis criterion: `tests/0016-allowlist/intro-counts.txt` (from git log) and `over-intro.txt` (build, magic, stdlib not yet shorter; ceilings only fall). Blockers: `construct` has no site table (its pins are orphan `construct:*` keys), `readonly` waits on E3.
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
