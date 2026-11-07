+++
type = "review"
id = "0016-review"
title = "RFC-0016 Wave 1 (0.9.2) code review ledger"
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
| D1 | High | open (CR-D, after CR-A/B) | The arithmetic-scope decision is made in four places with two state representations: parse-time `scopeChecked`/`withCheckDeclines`/`ParseCtx.ovfChecked`, and walk-time `currentArithWraps`/`arithCheckedHere`. The walk-time state is a global saved and restored around routine bodies, and `blkArith` sits on every `isBlock`. | `dsl_parser.nim:1257,1466,1494,5900,19907`; `runtime.nim:8808,23946,28773`; `types.nim:1324`. |
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

Fix commits `24d514c2`, `2cdb66b6`, `490c80b1` and `2bb912d4` were merged onto d9086529. On the merged tree, 16 touched suites and `check-readme-kinds.sh` all returned rc=0. D1 remains open; it goes to round 2 together with the re-review of this delta.

