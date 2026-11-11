+++
type = "review"
id = "0016-review"
title = "RFC-0016 code review ledger (0.9.2 Wave 1; 0.10.0 Waves 2-3)"
state = "pending"
profile = "rfc-flow@6"
+++

# RFC-0016 Wave 1 code review ledger

**Surface:** `e769b87d..d9086529` (`v0.9.1` to the post-wiring-audit head): `src/`, `tests/s8cu_helpers.nim`, `tests/k1lite.nim`, `scripts/k1lite.sh`, `scripts/check-readme-kinds.sh`, `.github/workflows/*.yaml`.

**Mandate:** the default one, from the standing `/loop` instruction. Fix everything through Medium and leave the Lows, except the cheap ones, which are batched.

## Round 1 (base d9086529)

Four lenses ran: correctness and soundness, security, design and ergonomics, and liveness. Adversarial verifiers then ran on SC1, SC2 and D2.

| id | sev | status | finding | evidence / fix |
|---|---|---|---|---|
| SC2 | High | fixed (CR-A 24d514c2) | A generic exception type collapses to its last type argument in `typeIdOf`. `G[ValueError]` raised under `except ValueError` is caught by the walker but not natively, which gives a trusted false `sxSat`. | `dsl_parser.nim:1631`, bracket case ~1669. Used for the raise id ~20743 and the except match ~20773. Confirmed by probe. |
| D1 | High | fixed (D1a ccc2fdec, D1b 773f3558) | The arithmetic-scope decision is made in four places with two state representations: parse-time `scopeChecked`/`withCheckDeclines`/`ParseCtx.ovfChecked`, and walk-time `currentArithWraps`/`arithCheckedHere`. The walk-time state is a global saved and restored around routine bodies, and `blkArith` sits on every `isBlock`. | `dsl_parser.nim:1257,1466,1494,5900,19907`; `runtime.nim:8808,23946,28773`; `types.nim:1324`. |
| M1 | Medium | refuted (CR-B) | `symexFind`'s macro output writes the deprecated `fromCache: false`, which was expected to warn at every user call site. | Nim 2.2.10 does not warn on a deprecated field in an object constructor, macro-built or not. The initialisers were dropped anyway, and `tsymex_0016_crb_macro_deprecation` guards against a regression. |
| M2 | Medium | fixed (CR-C 490c80b1) | Only `ubIndeterminateRead` can ride a witness, but the README implies all six kinds can. There is no end-to-end test of a real noinit witness through render, cache and `assertCoveredBy`; the render test builds its finding by hand. | `runtime.nim:~9428`; `tests/tsymex_0016_wa_runtime.nim:~50`; `README:414-432`. |
| M3 | Medium | fixed (CR-B 2cdb66b6) | Three module-wide `{.push warning[Deprecated]: off.}` cover about 40k lines, and two of them are never popped. | `types.nim:7`, `canonicalize.nim:19`, `runtime.nim:19`. |
| M4 | Medium | fixed (CR-B 2cdb66b6) | `buildprofile.Admission` is a stringly-typed tuple whose exported name collides with `coverage.Admission`. | `buildprofile.nim:125`, `coverage.nim:689`. |
| M5 | Medium | fixed (CR-C 490c80b1) | K1-0 runs on the c row only in CI, while the RFC row names three. cpp is added to CI; Z3 4.13.4 stays a by-hand release row until CI-B. | `symex-linux.yaml:113-126`. |
| M6 | Medium | fixed (CR-C 490c80b1) | `check-readme-kinds.sh` claims full kind coverage but checks only `fe*`/`ub*`. It has no negative test, and `paths-ignore: docs/**` means a README edit never runs it. | `scripts/check-readme-kinds.sh:24-28`. |
| L4 | Low | fixed (CR-C) | A stale "unproduced" comment. The lattice test treats a mention of a kind as its producer. `ubFloatToIntRange` has no producer, as documented. | `types.nim:2886`; `tsymex_rfc0005_s1_lattice.nim:109`. |
| L5 | Low | fixed (CR-C) | The remediation text names a replay as the reason for `witnessUndefined` and for crash-claim witnesses that are not host-runnable. | `symex.nim:~4184`; `render.nim:~408`. |
| L6 | Low | fixed (CR-C) | The `feLocalPragma` message cites a README heading that does not exist. | `dsl_parser.nim:~20093`. |
| L7 | Low | fixed (CR-C) | The docs recommend `-d:nelliFwrapv`, which is unimplemented (K5a). | `README:~429`; `types.nim:~2895,~5967`. |
| L9 | Low | open | Latent: `loweringPendingUb` is gated on `loweringPendingTaint != {}`. | `runtime.nim:19751,19806,19921,25826`. |
| SEC1 | Low | fixed (CR-C) | `prepareProbe` uses a predictable temp dir. | `tests/s8cu_helpers.nim`. |
| SEC2 | Low | fixed (CR-C) | The workflows have no `permissions:` block and keep the persisted checkout token. | `symex-linux.yaml`, `fuzzer-msvc.yaml`. |
| SEC3 | Low | fixed (CR-C) | `k1lite.sh` splices `-b` and `-t` into a `bash -c` string. | `scripts/k1lite.sh`. |
| SC3 | Low | open | Precision: the opaque-callee scan lists `OverflowDefect`/`DivByZeroDefect` for the signed magics in checks-off builds. Replay validates these, so this is not a soundness issue. | `dsl_parser.nim:~4144,4279`. |
| D7-D9 | Low | open | `buildWraps()` is read from a global constant at 8 sites. `renderBuildFlags` takes 9 positional arguments. `withCheckDeclines` does three jobs. These are folded into CR-D where they touch it. | design lens. |
| D2 | - | refuted | Scope leak on an exception: every exception escaping the walk ends the run (`runSymexCaught` `runtime.nim:28425-28619`), and `:28773` resets the scope before the next run reads it. The design point is kept under D1. | verifier. |
| SC1 | - | refuted | A routine-local `{.global.}` gives a false trusted SAT on a fresh process: no. The walker havocs it (`feGlobalHavoc`), and replay refutes it (`sxUnknown`). | verifier probe. |
| SC1b | Medium | out-of-scope | Predates Wave 1. A fork replay inherits the host's current value of a routine `{.global.}`, so after earlier host calls a SAT can be confirmed from run history, with no `runDependence`. Filed as RFC-0016 INT-40. | `tsymex_rfc0005_s8be_remainder.nim` pins only the reset target. |
| D4 | - | out-of-scope | The `arithChecks` default and contract are tangled. The field is deprecated and removed in a later wave, so this goes no further. | design lens. |
| D6 | - | wontfix | `buildSemantics` is import-order sensitive. Decided at WA-A P3, documented and pinned (`tsymex_0016_wa_importpush`). | |
| N1 | Medium | fixed (CR-E 2bb912d4) | `symexFindAllWitnesses` and `symexForAll` fail to compile on a SUT with no parameters. Found while fixing M2. `concolicAssist` refuses zero parameters by design. | `symex.nim:~4677`, `~1159`; `tsymex_0016_cr_zeroarg`. |
| N2 | Low | out-of-scope | `newLit(settings)` in `symexFind`'s expansion raises an `arithChecks` Deprecated warning from inside Nim's `macros.nim`. | Filed as RFC-0016 INT-41. |
| SC2b | - | precision | CR-A declines every non-`ref`/`ptr` bracket exception type. A full instantiated model is filed as PRC-38. | |

Fix commits `24d514c2`, `2cdb66b6`, `490c80b1` and `2bb912d4` were merged onto d9086529. On the merged tree, 16 touched suites and `check-readme-kinds.sh` all returned rc=0. D1 was fixed as a refactor under green: the walker scope became a lexical stack read through `wraps()` and `checked()`, and the parser computes it through a single pure function, `arithScopeFor`. The 12 joint suites and the CR2 pin returned rc 0, with no walker bump. The D7 and D9 parts that D1 touched are folded in; D8 (`renderBuildFlags` arity) stays Low.


## Round 2 (delta d9086529..b1bab060)

Four lenses ran: correctness, security, design and liveness. Adversarial verifiers then checked every finding at Medium or above.

| id | sev | status | finding | evidence / fix |
|---|---|---|---|---|
| R2-01 | Low | fixed (6a242791) | The parser's `overflowChecked` reads `asBuild` as unchecked, but in a checks-on build `asBuild` is checked. Every current reader guards on `buildWraps()`, so the hazard is latent. A design lens filed it as Medium; the verifier confirmed it and downgraded it to Low. | `buildWraps()` is folded into `overflowChecked`; `ordinalUnchecked` derives from it. |
| R2-02 | - | refuted | `pushArith` maps `asInherit` to checked with no guard. It is private, and its single caller filters out `asInherit`. | A `doAssert sc != asInherit` was added anyway (6a242791). |
| R2-03 | Low | open | `arithStamp` recomputes the scope with a dummy caller instead of deriving the stamp from the parser's resolved push. | `dsl_parser.nim:~1496`. |
| R2-04 | Low | open | `hostRefusalReason` re-enumerates `hostRunnable`'s conjuncts, and the crash-claim wording is duplicated in `render.nim`. | `symex.nim:~3935`. |
| R2-05 | Low | open | `effectiveArithChecks` reads the raw field; "effective" suggests a resolved value. | `types.nim:~5979`. |
| R2-06 | Low | open | `BuildRefusal.field` is redundant with the reason text. | `buildprofile.nim:~125`. |
| R2-07 | Low | open | `tsymex_0016_wa_undefined_e2e` runs only on the Linux C leg. It skips on cpp and under re-exec replay. | Inherent to stack-layout-dependent noinit reads. |
| R2-08 | Low | open | `tsymex_0016_cr_zeroarg` does not cover `concolicCollect`/`concolicFlip`. | `symex.nim:3852-3900`. |
| R2-09 | Low | fixed (6a242791) | A stale comment in the e2e test said `symexFindAllWitnesses` needs a parameter. | |
| R2-10 | Low | open | `k1lite.sh -b` is not validated against `c|cpp`. Developer-run only; no privilege boundary. | `scripts/k1lite.sh`. |

**Floor reached at round 2:** 0 Critical, 0 High and 0 Medium inside the surface. The 12 touched suites returned rc=0 at 6a242791. The open Lows (R2-03 to R2-08, R2-10, L9, SC3, D8) carry into Wave 2 under INT-42.

# 0.10.0 review (Waves 2-3)

**Surface:** `882a6f73..a72c7334` (`v0.9.2` to main after W3-z int7): `src/`, `scripts/`, `.github/workflows/`, `tests/0016-allowlist/`, and the tests those changes added.

**Precondition:** the Wave 3 wiring audit ran this session over `v0.9.2..e707b09c`. Its findings were fixed in W3-z (int..int7), and `0016/wiring` stays `proven`.

**Mandate:** pending the operator's approval of the round 1 table.

## Round 1 (base a72c7334)

Six lenses ran: runtime soundness, parser soundness, replay and cache (opus); security, design, liveness (sonnet). Adversarial verifiers then ran on every Critical/High and on R-M1/R-M2. The soundness verifiers reproduced their findings with scratch tests at a72c7334 on linux-c.

| id | sev | status | finding | evidence |
|---|---|---|---|---|
| H1 | High | open | Closures that share an environment get split copies on the re-exec wire, so re-exec (the Windows default) can confirm a trusted false sxSat that fork refutes. | `replaywire.nim:157-216,255-316`: envs are not interned like refs at :237-243/:339-344. Reproduced with `-d:nelliReplayReexec`: sxSat trusted, while fork gives sxUnknown feReplayRefuted. |
| H2 | High | open | The tail walk drops `ubIndeterminateRead`. A `{.noinit.}` read after the label gives a trusted sxSat, rsNotNeeded, witnessUndefined {}. Regression from R2/R6. | `runtime.nim` ~30935 (`discard walk`), ~30948 (dcFreshSymbol exempt), :27786 (`noteUbAtFork` early return). Reproduced at x=0. |
| H3 | High | open | `modelPins` pins the opaque-call havoc epochs `heap_<k>@ep<n>` for n >= 1, so the candidate tail walk fixes a callee effect to the explore model's value. This hides UB the real run executes: trusted sxSat, rsConfirmed. | `runtime.nim:13266` (6490a48b, in the surface). A/B: pinning epoch 0 only gives untrusted with ubSignedOverflow. The cell has to be read before the label too. |
| H4 | High | open | The P17 guard snapshots any non-symbol loop bound. Nim re-reads field paths and var params on every iteration, so the trip count is wrong and trusted. | `dsl_parser.nim` ~21227 and ~21274. Var param n: native g(5)=1, the engine proves "one" UNSAT, trusted. `o.n` and `countup(0,o.n)` likewise. `p[]` is modelled correctly. |
| H5 | High (raised from Medium: trusted false proof) | open | A routine `{.noinit.}` is admitted as read, but `result` is still zero-initialised. | `pragmaaxes.nim` routine read row. f(false) natively 4663; the engine proves `v == 0` trusted. |
| H6 | High (raised from Medium: trusted false proof) | open | An enum with a negative ordinal is sized by bit width, but Nim makes it 4 bytes. A cross-arm read of such a field reads 1 byte, sign-extended. | `variant_layout.nim` scalar; `dsl_typebridge.nim:440`. Native ord(o.e)=255; the engine proves it UNSAT, trusted. The discriminator form does not compile (refuted). |
| H7 | High (raised from Low-Medium: trusted false proof) | open | `mayWriteMagics` omits `mSetLengthSeqUninit`, so `lentLoopDecline` misses `setLenUninit(s, 0)` in a `for x in s` body. | `dsl_parser.nim:16002`. With `seq[string]`, native reaches "other"; the engine finds "one", trusted. |
| R-M1 | Medium | open | `rowOf` admits `--exceptions:setjmp` on Windows (brMingw/brMsvc), although the build cell says Windows crashes (INT-12). | `buildprofile.nim:399-400`, `:600-602`; INT-12 is open in the RFC at :833. The result is a crash, not a wrong verdict. |
| L-M1 | Medium | open | A `rows=`-scoped allowlist entry is outside the ratchet. Nothing caps the entries, requires a proper subset of rows, or requires the evidencing row to be named. | `tsymex_0016_allowlist_ceilings.nim:34`; `tsymex_0016_universe.nim:296-310,377`. 12 entries. |
| L-M2 | Medium | open | The wall-time ceiling is one-sided: a listed offender has no upper bound, and the nightly report passes when zero merged legs download. | `check-ceiling.sh:109-124`; `symex-nightly.yaml:539-541`. |
| L-M3 | Medium | open | 12 producer-less error kinds carry the misleading allowlist reason "no pinDecline asserts this kind" (deletion is deferred to W-64). | `types.nim` classOf rows; `0016-allowlist/errorkind.txt:8,39,40,49,50`. |
| L-M4 | Medium | open | A `never` cell is evidenced by a literal `holds = true`, and `evidences` accepts any pvCrashed record for any declined/never cell regardless of kind. | `tsymex_0016_k5b_refusals.nim:149`; `s8cu_helpers.nim:881-891`; `tsymex_0016_universe.nim:268-275`. |
| D1 | High (design) | open | The arithmetic-regime decision is made in several places under four vocabularies (`ArithScope`, `WalkArith`, `DefProfile`, `buildWraps`). | `types.nim:1379`; `dsl_parser.nim:1598,1672,21585`; `runtime.nim:2152,2187,9369`; 18 `buildWraps()` sites. |
| D2 | Medium (design) | open | `ArithScopeProof` can be minted by anyone through `replayArith`. | `types.nim:3498-3530,5266`. |
| D3 | High (design) | open | `dsl_parser.nim` (25k lines) and `runtime.nim` (33.5k lines) keep growing. The UB-deposit policy is inline, the walk-units log I/O is in the walker, and the `include` files share one namespace. | `dsl_parser.nim:4701-4817`; `runtime.nim:14905,30896`. |
| D4 | Medium (design) | open | Error-kind properties (class, severity) live away from the enum, and severity is set by each caller. | `errorkind.nim`; `types.nim:2203,2505`. |
| D5 | Medium (design) | open | The axis modules re-implement keys and verbs, and have lateral dependencies (`definedness` imports `magic_rows`). `check_options` mixes the pure scan with compile-time I/O. | `magic_rows.nim:32-35`; `check_options.nim:254,763-871`. |
| D6 | Medium (design) | open | `symex.nim` (6.2k lines) is both the facade and the implementation (held-set walk, routine table). | `symex.nim` diff. |
| R-M2 | Low | refuted as stated | The layout pragma is missing from the cache key. A packed or union variant is declined, and the decline text is keyed. Residual: `{.align.}`/`size` may change a verdict without changing the key, under fieldChecks:off c only; untraced. | `pragmaaxes.nim:170`; `dsl_parser.nim:18352-18467`. |
| L1 | Low | open | ccFamily (mingw vs msvc) is not in the cache key, and a hit is stamped with the current row. | `buildprofile.nim` buildSegment. |
| L2 | Low | open | A non-closure proc slot read back as nil is not rejected (hardening). | `replaywire.nim` wireGet proc arm. |
| L3 | Low | open | `RawWitness.pinsComplete` is computed and never read. | `runtime.nim:13184,16659`. |
| L4 | Low | open | `isNilPtrCast` accepts any target type; `routinePragmaReason` calls `get` on an option that may be none. | `dsl_parser.nim`. |
| L5 | Low | open | Dead exports: `opaqueBodyDefinedness`, `admitConstruct`, `magicIn`, `checkNames`. | `definedness.nim:335`; `constructaxes.nim:156`. |
| L6 | Low | open | Fuzz `undefinedFindings`/`annotationViolations` are not in the default campaign summary. | `fuzz.nim:836,2589-2590,2833`. |
| L7 | Low | open | The walker bumps 344 and 349 have no floor pin; `orphanCells` is report-only; the cpp/z3/msvc rows are nightly-only on main. | `canonicalize.nim:590-595`; `tsymex_0016_universe.nim:454`. |
| S1 | Low | open | The `k8a-nightly.sh` workflow_dispatch `tag` input is passed to git unvalidated (needs dispatch rights). | `k8a-nightly.sh:233`. |
| S2 | Low | open | First-party actions are pinned by major tag, not by SHA. | `.github/workflows/*`. |
