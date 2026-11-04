+++
type  = "review"
id    = "0005-review"
title = "RFC-0005 code review ledger (0.9.1)"
state = "pending"
profile = "rfc-flow@6"
+++

# RFC-0005 code review ledger (0.9.1)

**Surface (fixed for the whole loop).**
`549dae8b7998985588b4cb7e6033cd52ffbcef68..edb1277f8ba3652778c98d5b6ccb8788a7db0396`
(v0.8.0 to the 0.9.1 integration head, wiring proven), paths `src/**`. That
is 43 files, +67,396/−6,767. The review is run after the fact: v0.9.0 shipped
without it, and its findings land in 0.9.1. Tests and docs are in scope only
as evidence.

**Rounds.**
- Round 1: the surface itself. Fixes landed a5e5d6ad..54cbb358, recorded in the next commit (mandate:
  through Medium, 2026-11-04). Round 2 re-reviews that delta.

## Findings

| ID | Sev | Status | Lens | File | Finding | Test / reason |
|---|---|---|---|---|---|---|
| R1-01 | Critical | fixed | front end | `dsl_parser.nim` ~19058 (stmt `if`), ~12640 (`nnkIfExpr`), ~15932 (iterator `if`), ~5657 (`hoistCaseExpr`) | An `elif` condition's preamble (a seq bounds fork, a user call) is hoisted above the whole `if`, so it runs before the first condition is tested | Verified by run: `if i>=s.len: <label> elif s[i]==3` gives `sxRaised IndexDefect` on `s=@[],i=0`, trusted (native reaches the label); a `var`-seq call in the `elif` gives a clean false `sxUnsat`. Same on main; bfbc34e1; `tsymex_rfc0005_r1_elif_preamble` |
| R1-02 | Critical | fixed | front end | `dsl_parser.nim` ~12583-12592 | `succ`/`pred` on an enum or char lower to plain `+`/`-` with no bound check | Verified by run: native `OverflowDefect`; symex gives `sxUnsat` for `tRaisedExn("OverflowDefect")`, and a false `sxSat` on a char label. Same lowering on main (read); 00101ddb + 0f89a68f (var-parameter regression caught by the round gate); `tsymex_rfc0005_r1_succ_pred` |
| R1-03 | Critical | fixed | PCRE | `pcre_syntax.nim`, `pcre_select.nim` | PCRE's compile limits ("regular expression is too large", nesting > 250) are not modelled, so patterns native rejects get clean verdicts | Verified by run: 300 nested parens give `sxSat "a"`, trusted; `(?:[a-z]){1700}\|b` gives `sxSat "b"`; `except RegexError` target gives `sxUnsat`. Same on main. Related: RFC-0016 CRH-04; c9682ebc; `tsymex_rfc0005_r1_pcrelimits` (boundary sweep against `re()`); also closes RFC-0016 CRH-04 |
| R1-04 | Critical | fixed | walker | `runtime.nim` ~22649 (`isVariantConstructSym`, raw `lower` per survivor) | On a branch fork, a variant construction's plain-field degrade taint (unwritten global) is lost | Verified by run: `if b>3: let p = Pkt(opcode: op, tag: gN); if p.tag == 5: <label>` gives `sxSat`, `pathTaint={}`, trusted; native never reaches it. Same on main. The Table-key site (~21384) did not reproduce; 222b78af; `tsymex_rfc0005_r1_lowertaint` (each statement owns the pending lowering taint) |
| R1-05 | High | fixed | PCRE | `pcre_code.nim` 179-215, reached from `pcre_select.nim` 992/1059/3975, `regex_parser.nim` 962 | Counted groups are expanded before the NFA cap: a resource-exhaustion risk for the test host | Verified by run: 200^3 nesting took 33.6 s and peaked at 5.7 GB before declining; larger shapes inferred; c9682ebc; `tsymex_rfc0005_r1_pcrelimits` |
| R1-06 | High | fixed | design | `replayproc.nim` 86-149; `symex.nim` ~3230, ~3292, ~3413 | The replay outcome is returned through threadvars that the settle must read in order | Design; make `ReplayOutcome` a value; d8969822; `ReplayResult` value, `replayresult.nim` |
| R1-07 | High | fixed | design | `runtime.nim` 13939/13950; `symex.nim` ~550/~646/~751 | Run-dependence is three threadvars read at save time; a public `saveSymexVerdict` after other work reads another run's flags | Design; carry it on `Soundness`; d8969822; `Soundness.runDependence`; `tsymex_rfc0005_r1_rundependence` |
| R1-08 | Medium | fixed | settle/cache | `canonicalize.nim` ~6487 | The cache key omits the build flags that decide whether `fn` raises (`-d:danger`, `--assertions:off`, check flags), so a debug-build `rsConfirmed` can be served trusted to a danger build | Verified by reading; aaf3733f; `|bf=` segment; `tsymex_rfc0005_r1_keyflags` |
| R1-09 | Medium | fixed | settle/cache | `canonicalize.nim` ~6320 | The cache key covers the parsed IR only; `rsConfirmed`/`witnessUnsafe` are facts about the real `fn`, including opaque callee bodies | Reading; b19ea30e; `;impl=` callee digest (`impl_digest.nim`), importc bodies and proc-value targets documented as unkeyed; `tsymex_rfc0005_r1_keyimpl` |
| R1-10 | Medium | fixed | design | `engine/types.nim` 284-291; `symex.nim` ~991 | The finding sink threadvar is never drained by the engine; `assertCoveredBy` findings leak into a later `symexForAll` report | Verified by run; same on main; dd30ee50; sink removed, findings returned by value; `tsymex_rfc0005_r1_findingapi` |
| R1-11 | Medium | fixed | liveness | `symex.nim` ~4245/4276/4313/4359/4391 | The cache-key and DB macros skip `methodPrelude`; a method-dispatch SUT's key differs from `symexFindAllWitnesses`' and is order-dependent | Reading; b19ea30e; one `entryParse` helper; `tsymex_rfc0005_r1_keymethod` |
| R1-12 | Medium | fixed | liveness | `runtime.nim` 7988, `resetSymexRunState` ~28134 | `pendingPtrCompares` is not reset per run; stale ASTs from a freed context could reach `checkedEq` | Unverified: no abort shape was constructed; 08e40fc8; reset added with eight other walk-scoped threadvars; no test (abort shape not constructible) |
| R1-13 | Medium | fixed | walker | `runtime.nim` ~27389 | `lowerVariantFieldSet` declines with a `dcOmitted` kind but the path continues with the write dropped and no taint | Unverified; 69c2f0a1; not reproduced on a clean path, site reclassified to `feUnsupportedOp` (`dcSubstituted`); `tsymex_rfc0005_r1_variantset` |
| R1-14 | Medium | fixed | design | replay types across `replayproc`, `symex`, `soundness` | About eight overlapping replay types, mapped by hand; message text repeats the kind names | Design; d8969822; `replayresult.nim` owns the replay result and its mappings |
| R1-15 | Medium | fixed | design | `symex.nim` ~4059-4093 | `status` and `trusted()` are two signals; `assertCoveredBy` acts on `status` alone and splats an `rsUnconfirmed` lossy witness | Reading; dd30ee50; `assertCoveredBy` decides on `trusted()`; `tsymex_rfc0005_r1_findingapi` |
| R1-16 | Medium | fixed | design | `soundness.nim` 127-133; `engine/types.nim` 259 | A zero `Soundness` reads as trusted, so a forgotten field fails open | Reading; d390f119; `rsUnsettled` zero value, fixed code table keeps old records; `tsymex_rfc0005_r1_findingapi` |
| R1-17 | Medium | fixed | design | `engine/types.nim` ~55-100 | `SymexFinding` drops the budget `bounds` that make an `sxUnsat` a proof | Reading; 50ebce5b; `bounds` carried and rendered; `tsymex_rfc0005_r1_findingapi` |
| R1-18 | Medium | fixed | security | `replayproc.nim` 202, 343, 419-462, 849 | One `H` byte per hit, and the host re-decodes the whole buffer: quadratic, overruns the deadline, unbounded memory with no timeout | Reading; c2e7751f; `tsymex_rfc0005_r1_replaychild` |
| R1-19 | Medium | fixed | security | `replayproc.nim` 436-443, 743-761 | A lost wait status reports a signalled child as exit 0; on POSIX re-exec, `waitpid` -1 is unhandled: it spins, then kills a possibly reused pid | Reading; c2e7751f; `tsymex_rfc0005_r1_replaychild` (+ `_reexec`) |
| R1-20 | Medium | fixed | security | `replayproc.nim` 821-873 | Re-exec temp files have predictable names in the shared temp dir: symlink, TOCTOU, forged output | Reading; c2e7751f; `tsymex_rfc0005_r1_replaychild_reexec` |
| R1-21 | Medium | fixed | security | `replayproc.nim` ~610, ~626 | Windows `bInheritHandles=TRUE` hands every inheritable host handle to the child and SUT | Reading; c2e7751f; `PROC_THREAD_ATTRIBUTE_HANDLE_LIST`; cross-compiled, proven by the Windows legs |
| R1-22 | Medium | fixed | PCRE | `pcre_syntax.nim` 1160-1380; `pcre_code.nim` 78-91; `pcre_select.nim` 665 | Unbounded reader recursion (host stack overflow); `codeSize` int overflow before the cap | Reading; c9682ebc + 9663105d; `tsymex_rfc0005_r1_pcrelimits` |
| R1-23 | Low | fixed | security | `replayproc.nim` 462-464, 559, 801 | `NELLI_REPLAY_CHILD` from the user's environment: a stale marker refuses every replay; Windows appends a duplicate; a `\|` in a path breaks the spec | Reading; c2e7751f; per-spawn nonce marker; `tsymex_rfc0005_r1_replaychild` |
| R1-24 | Low | open | security | `replayproc.nim` 448-453 | SUT-started grandchildren survive when the child ends by itself | Reading |
| R1-25 | Low | open | liveness | `runtime.nim` 29666 | `ConcolicCollectResult.annotationViolations` has no reader on the fuzzer path | Reading |
| R1-26 | Low | open | liveness | `engine/targeting.nim` 390 | `saveSecondary` is unguarded, so the new `DbError` escapes `forAll` | Reading |
| R1-27 | Low | open | liveness | `runtime.nim` 29723 | The concolic flip solve lacks `maxSeqLen`/`seqQueryRLimit` and the theory facts `trySolve` adds | Reading |
| R1-28 | Low | open | design | `engine/types.nim` 106, 122 | `FindingHint`/`FindingGap` kinds are strings | Design |
| R1-29 | Low | open | design | `runtime_*` includes; `symex.nim` | Include-split modules; `symex.nim` mixes codegen, cache codecs and settle | Design |
| R1-30 | Low | fixed | security | `replayproc.nim` 362 | An uncaught `parseInt` in `decodeChild` leaks an fd and a zombie | Reading; c2e7751f |
| R1-31 | Low | open | security | `replayproc.nim` 301-313 | No memory cap on macOS/BSD; no CPU/FSIZE/NPROC limits; no Windows `ActiveProcessLimit` | Reading |
| R1-32 | Low | open | security | `replayproc.nim` 297, 386, ~645, ~710; `replaywire.nim` 38-106 | `pipe2`, `PDEATHSIG` thread, `WaitForSingleObject` wrap, `resumeThread`, wire length overflow, "(deleted)" exe, non-atomic counter | Reading |
| R1-33 | Low | open | settle/cache | `symex.nim` ~916, ~315, `storedGaps`; `replayproc.nim` ~146; `saveSymexRaisedImpl`; `winnerLossy` | Stale "trusted by construction" comment; unenforced one-digit codec; `storedGaps` prefix; `reSignalled` not run-dependent; first-soundness-per-type; lossy sibling precision | Reading |
| R1-34 | Low | open | liveness | `render.nim` 78-81, 202-205; `parallel.nim` | `witnessUnsafe` is not rendered; `spinJitter` is now up to about 100 syscalls per op; the `ReplayOutcome` doc says "three-valued" | Reading |
| R1-35 | — | refuted | walker | `runtime.nim` ~21384 | T1 trigger B: a Table key read from an unwritten global loses its taint | Refuted by run: `sxSat {scSpurious} rsConfirmed`, correctly tainted |
