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
- Round 1: the surface itself.

## Findings

| ID | Sev | Status | Lens | File | Finding | Test / reason |
|---|---|---|---|---|---|---|
| R1-01 | Critical | open | front end | `dsl_parser.nim` ~19058 (stmt `if`), ~12640 (`nnkIfExpr`), ~15932 (iterator `if`), ~5657 (`hoistCaseExpr`) | An `elif` condition's preamble (a seq bounds fork, a user call) is hoisted above the whole `if`, so it runs before the first condition is tested | Verified by run: `if i>=s.len: <label> elif s[i]==3` gives `sxRaised IndexDefect` on `s=@[],i=0`, trusted (native reaches the label); a `var`-seq call in the `elif` gives a clean false `sxUnsat`. Same on main |
| R1-02 | Critical | open | front end | `dsl_parser.nim` ~12583-12592 | `succ`/`pred` on an enum or char lower to plain `+`/`-` with no bound check | Verified by run: native `OverflowDefect`; symex gives `sxUnsat` for `tRaisedExn("OverflowDefect")`, and a false `sxSat` on a char label. Same lowering on main (read) |
| R1-03 | Critical | open | PCRE | `pcre_syntax.nim`, `pcre_select.nim` | PCRE's compile limits ("regular expression is too large", nesting > 250) are not modelled, so patterns native rejects get clean verdicts | Verified by run: 300 nested parens give `sxSat "a"`, trusted; `(?:[a-z]){1700}\|b` gives `sxSat "b"`; `except RegexError` target gives `sxUnsat`. Same on main. Related: RFC-0016 CRH-04 |
| R1-04 | Critical | open | walker | `runtime.nim` ~22649 (`isVariantConstructSym`, raw `lower` per survivor) | On a branch fork, a variant construction's plain-field degrade taint (unwritten global) is lost | Verified by run: `if b>3: let p = Pkt(opcode: op, tag: gN); if p.tag == 5: <label>` gives `sxSat`, `pathTaint={}`, trusted; native never reaches it. Same on main. The Table-key site (~21384) did not reproduce |
| R1-05 | High | open | PCRE | `pcre_code.nim` 179-215, reached from `pcre_select.nim` 992/1059/3975, `regex_parser.nim` 962 | Counted groups are expanded before the NFA cap: a resource-exhaustion risk for the test host | Verified by run: 200^3 nesting took 33.6 s and peaked at 5.7 GB before declining; larger shapes inferred |
| R1-06 | High | open | design | `replayproc.nim` 86-149; `symex.nim` ~3230, ~3292, ~3413 | The replay outcome is returned through threadvars that the settle must read in order | Design; make `ReplayOutcome` a value |
| R1-07 | High | open | design | `runtime.nim` 13939/13950; `symex.nim` ~550/~646/~751 | Run-dependence is three threadvars read at save time; a public `saveSymexVerdict` after other work reads another run's flags | Design; carry it on `Soundness` |
| R1-08 | Medium | open | settle/cache | `canonicalize.nim` ~6487 | The cache key omits the build flags that decide whether `fn` raises (`-d:danger`, `--assertions:off`, check flags), so a debug-build `rsConfirmed` can be served trusted to a danger build | Verified by reading |
| R1-09 | Medium | open | settle/cache | `canonicalize.nim` ~6320 | The cache key covers the parsed IR only; `rsConfirmed`/`witnessUnsafe` are facts about the real `fn`, including opaque callee bodies | Reading |
| R1-10 | Medium | open | design | `engine/types.nim` 284-291; `symex.nim` ~991 | The finding sink threadvar is never drained by the engine; `assertCoveredBy` findings leak into a later `symexForAll` report | Verified by run; same on main |
| R1-11 | Medium | open | liveness | `symex.nim` ~4245/4276/4313/4359/4391 | The cache-key and DB macros skip `methodPrelude`; a method-dispatch SUT's key differs from `symexFindAllWitnesses`' and is order-dependent | Reading |
| R1-12 | Medium | open | liveness | `runtime.nim` 7988, `resetSymexRunState` ~28134 | `pendingPtrCompares` is not reset per run; stale ASTs from a freed context could reach `checkedEq` | Unverified: no abort shape was constructed |
| R1-13 | Medium | open | walker | `runtime.nim` ~27389 | `lowerVariantFieldSet` declines with a `dcOmitted` kind but the path continues with the write dropped and no taint | Unverified |
| R1-14 | Medium | open | design | replay types across `replayproc`, `symex`, `soundness` | About eight overlapping replay types, mapped by hand; message text repeats the kind names | Design |
| R1-15 | Medium | open | design | `symex.nim` ~4059-4093 | `status` and `trusted()` are two signals; `assertCoveredBy` acts on `status` alone and splats an `rsUnconfirmed` lossy witness | Reading |
| R1-16 | Medium | open | design | `soundness.nim` 127-133; `engine/types.nim` 259 | A zero `Soundness` reads as trusted, so a forgotten field fails open | Reading |
| R1-17 | Medium | open | design | `engine/types.nim` ~55-100 | `SymexFinding` drops the budget `bounds` that make an `sxUnsat` a proof | Reading |
| R1-18 | Medium | open | security | `replayproc.nim` 202, 343, 419-462, 849 | One `H` byte per hit, and the host re-decodes the whole buffer: quadratic, overruns the deadline, unbounded memory with no timeout | Reading |
| R1-19 | Medium | open | security | `replayproc.nim` 436-443, 743-761 | A lost wait status reports a signalled child as exit 0; on POSIX re-exec, `waitpid` -1 is unhandled: it spins, then kills a possibly reused pid | Reading |
| R1-20 | Medium | open | security | `replayproc.nim` 821-873 | Re-exec temp files have predictable names in the shared temp dir: symlink, TOCTOU, forged output | Reading |
| R1-21 | Medium | open | security | `replayproc.nim` ~610, ~626 | Windows `bInheritHandles=TRUE` hands every inheritable host handle to the child and SUT | Reading |
| R1-22 | Medium | open | PCRE | `pcre_syntax.nim` 1160-1380; `pcre_code.nim` 78-91; `pcre_select.nim` 665 | Unbounded reader recursion (host stack overflow); `codeSize` int overflow before the cap | Reading |
| R1-23 | Low | open | security | `replayproc.nim` 462-464, 559, 801 | `NELLI_REPLAY_CHILD` from the user's environment: a stale marker refuses every replay; Windows appends a duplicate; a `\|` in a path breaks the spec | Reading |
| R1-24 | Low | open | security | `replayproc.nim` 448-453 | SUT-started grandchildren survive when the child ends by itself | Reading |
| R1-25 | Low | open | liveness | `runtime.nim` 29666 | `ConcolicCollectResult.annotationViolations` has no reader on the fuzzer path | Reading |
| R1-26 | Low | open | liveness | `engine/targeting.nim` 390 | `saveSecondary` is unguarded, so the new `DbError` escapes `forAll` | Reading |
| R1-27 | Low | open | liveness | `runtime.nim` 29723 | The concolic flip solve lacks `maxSeqLen`/`seqQueryRLimit` and the theory facts `trySolve` adds | Reading |
| R1-28 | Low | open | design | `engine/types.nim` 106, 122 | `FindingHint`/`FindingGap` kinds are strings | Design |
| R1-29 | Low | open | design | `runtime_*` includes; `symex.nim` | Include-split modules; `symex.nim` mixes codegen, cache codecs and settle | Design |
| R1-30 | Low | open | security | `replayproc.nim` 362 | An uncaught `parseInt` in `decodeChild` leaks an fd and a zombie | Reading |
| R1-31 | Low | open | security | `replayproc.nim` 301-313 | No memory cap on macOS/BSD; no CPU/FSIZE/NPROC limits; no Windows `ActiveProcessLimit` | Reading |
| R1-32 | Low | open | security | `replayproc.nim` 297, 386, ~645, ~710; `replaywire.nim` 38-106 | `pipe2`, `PDEATHSIG` thread, `WaitForSingleObject` wrap, `resumeThread`, wire length overflow, "(deleted)" exe, non-atomic counter | Reading |
| R1-33 | Low | open | settle/cache | `symex.nim` ~916, ~315, `storedGaps`; `replayproc.nim` ~146; `saveSymexRaisedImpl`; `winnerLossy` | Stale "trusted by construction" comment; unenforced one-digit codec; `storedGaps` prefix; `reSignalled` not run-dependent; first-soundness-per-type; lossy sibling precision | Reading |
| R1-34 | Low | open | liveness | `render.nim` 78-81, 202-205; `parallel.nim` | `witnessUnsafe` is not rendered; `spinJitter` is now up to about 100 syscalls per op; the `ReplayOutcome` doc says "three-valued" | Reading |
| R1-35 | — | refuted | walker | `runtime.nim` ~21384 | T1 trigger B: a Table key read from an unwritten global loses its taint | Refuted by run: `sxSat {scSpurious} rsConfirmed`, correctly tainted |
