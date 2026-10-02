# Job: S8bi -- resume slice (S8bb's remainder A)

Branch `rfc-0005-s8bi`, checkpoint 719f2dc (base 9e15103 = rfc-0005-s8bb; walker 210).
Resume it in a worktree at origin/rfc-0005-s8bi. Read WORKER-BRIEF.md first.
The original scope is the S8bi row in docs/rfc/0005-branch-scoped-degrade.md: regex nodes as defect carriers, closure exit facts on earlier raises, newSeq[T](n) and notin set-literal targets, recursive-function fuel audit.
The 86-suite verification list is jobs/s8bi-suites.txt. `$S/...` paths in the note below are on the coordinator host; recreate the equivalents locally.
Finish per the "Next steps" section, then report DONE as worker-reports/s8bi.md.

## Handoff note from the previous agent

I've stopped my test runs (other agents' runs are still going), committed the work in progress and pushed it: `rfc-0005-s8bi` at `719f2dc6b138f4cadbfaa365a77d1b142323e2b2`. The base is 9e15103 (`origin/rfc-0005-s8bb`); `d0eb17b`, which adds the S8bi RFC row as pending, sits between the base and this commit. Walker is bumped to 210 and the CR2 pin now says `"210"`.

All five items are implemented and the new suite passes 45/45 on Z3 5.1 (c backend). Not done yet: the full targeted verification, any Z3 4.13.4 run, the cpp run, the Windows legs, the RFC "As landed (S8bi)" section, and flipping the row to done.

## Pins: RED at base, GREEN at the checkpoint

All are in `tests/tsymex_rfc0005_s8bi_remainder.nim`, registered in `nelli.nimble` after the s8bb entries. The base RED for items 1, 2, 4 and 5 came from running the suite on an export of 9e15103 (`$S/s8bi-base`); item 3 was taken from a separate probe, because newSeq crashes the compile at base.

| Item | Wrong at base | Now |
|---|---|---|
| 1 | `while b >= 0 and f(b)` with `f` raising: false sxSat | sxUnsat |
| 1 | Borrowed `div` behind `or` in a while guard: false sxSat | sxUnsat |
| 1 | `(*UTF8)` pattern behind `and`, in both if and while guards: sxUnknown | sxSat |
| 1 | `re(p)` behind `and`: sxUnknown | sxSat |
| 2 | `while ord(s[i]) + f(x) > 0` and `10 div i + f(x)`: index/div raise before the closure call gave false sxUnsat | sxSat |
| 2 | The closure's own "did not trap" fact applied to an earlier raise: false sxUnsat | sxSat |
| 2 | A raise before the call in a three-term expression: false sxUnsat | sxSat |
| 2 | `s[i] == chr(f(x))`: false sxUnsat | sxSat |
| 3 | Any `newSeq[T](n)`: compile abort ("node has no type", `dsl_typebridge.nim:838`) | modelled |
| 4 | Every set-literal pin: `feUnsupportedExprKind nnkCurly` | modelled |
| 5 | Source scan flags `regex_parser.nim` `run` and both `regexReplaceRec` definitions as fuel-less | all fueled |

Controls are green on both trees. The controls that guard against over-correction (a raise after the call still gets the call's facts) are sxUnsat as they should be.

## Design and root causes

1. **Raise-site predicate (`dsl_parser.nim`).**
   - `rhsHasInlineDefectFork` now returns true for: a closure call, a `map`/`filter` call over a closure, a borrowed `+ - * div mod`, every regex call except capture-group reads, and `newSeq`.
   - In a while guard nothing is hoisted, so this predicate is the only protection. At base those nodes were lowered on the flat fast path whether or not the short circuit reached them.
   - I made every non-capture regex call a raise site, not just undecided patterns. Valid patterns pay only the cost of the guarded form.
2. **Closure exit facts in evaluation order (`runtime.nim`).**
   - Each exit fact is now logged in `w.raiseOrder` as a new `rskClosureExit` entry, right after the call's own raise entries.
   - `drainScalarRaiseForks` takes the facts that `drainPendingLowerEffects` had appended off the end of the path, then puts them back as a stage at their logged position.
   - `drainClosureRaises` is simplified to match. `ClosureRaise.priorExitPc` is removed (it would otherwise be dormant).
   - If those facts are not found at the end of the path, it keeps the old behaviour and records a `weInternalWalkerFault`.
3. **A separate ordering bug I found and fixed here.** `parseAtomicOperand` keeps `s[i]` inline (for the CR-17(a) check), so a later operand's hoisted `let`s ran before it.
   - New helper `keepInlineRaiseOrder` adds an evaluation-only `let` of the inline operand before those hoisted lets, at all six operand-pair sites.
   - I kept the two `parseAtomicOperand` calls on separate lines, because `tsymex_phase15_A2a_chokepoint_audit` counts marker lines. A combined pair helper was the dead end here.
4. **`newSeq` family.**
   - New IR kind `iekSeqNew` (fields `snArg`, `snElemTy`, `snZeroed`, `snOfCap`), wired through every IR-kind site including the emit-roundtrip gate (two new fixtures there). The parser intercepts it before `ensureProcRegistered`, and the statement form `newSeq(s, n)` goes through the normal assignment path.
   - Lowering:
     - every form raises `RangeDefect` when `n < 0`;
     - `newSeq` builds a constant array of `default(T)`;
     - `newSeqOfCap` has length 0;
     - `newSeqUninit` uses a free array plus an `feUnsupportedOpHavoc` degrade;
     - an element type the walker can't store declines as `seNestedSeqUnsupported`.
5. **Set literals.** `parseSetLitMember` turns membership in a literal of constants into an OR of equalities and `>=`/`<=` range checks. The key is read once.
   - Membership never range-checks the key: 70000 in `{1, 3}` is false, which I confirmed in Nim.
   - A range over an inline `s[i]` is expanded into equalities instead, because CR-17 declines ordering comparisons on `s[i]`. Without this, the while-guard `notin` pin came back sxUnknown.
   - Non-constant elements and set-typed values still decline.
6. **Fuel.** In `runtime_strings.nim` `regexReplaceRec` (both definitions) and `regex_parser.nim` `run`, each recursive definition now takes `fuel: Z3Int`, has a `fuel <= mkInt(0)` base case, and passes `fuel - 1` on each recursive call, starting from `len + 1`. `rep` already had fuel.
   - The guard test scans `src/**/*.nim` code (comments stripped), checks every `defineRecFun[`, and forbids the raw API (`Z3_mk_rec_func_decl`, `Z3_add_rec_def`, `define-fun-rec`).
   - Fixture self-tests prove the scan rejects a fuel-less definition and accepts a fueled one.

## Partial verification

18 of 86 targeted suites finished on the checkpoint and 21 of 85 on base, all on Z3 5.1 with the c backend. Every finished suite had 0 failures, including CR2 and the three A2a audits.

## Next steps for the remote session

1. Run the 86 suites in `$S/bi/list.txt` (the brief's list plus the grep results) on the head and on a 9e15103 worktree, under both Z3 5.1 and 4.13.4, and diff them per check. Never run the same test file twice at once in one tree. `$S/bi/runone.sh` and `$S/bi/pass.sh` do this and write `summary.<mode>` files, but they use this host's paths. Priorities:
   - s8bb, s8ay, s8aw and s8bb_replace (these touch the fuel and regex-guard changes);
   - s7_closure and the closure/CR1_CR5 suites (the order change);
   - A2a and r1b (the extra `evalOrder` let);
   - also grep the logs for "closure raise drained on a path"; that message means the walker-fault fallback fired.
2. Run the new suite once with cpp, and time it. 166 s on this host includes compilation, so the brief's under-60 s per backend limit is unconfirmed.
3. Write "As landed (S8bi)" at the end of `docs/rfc/0005-branch-scoped-degrade.md` and flip the S8bi row to done. Under "Different mechanisms, reported and not fixed here":
   - SOUNDNESS: a huge `n` in `newSeq` is modelled as succeeding, where Nim runs out of memory or aborts.
   - PRECISION: set-typed values, `set[T]` params and builtin-set `incl`/`excl` are unclassified.
   - PRECISION: `let r = re"(ab"` declines as `feUnsupportedExprKind nnkCallStrLit`, although Nim always raises `RegexError` there.
   - PRECISION: `newSeqUninit` taints the whole path even when no element is read.
   - PRECISION: set literals with non-constant elements still decline.
4. Replace the WIP commit with a proper `feat(symex): RFC-0005 S8bi -- ...` commit (no trailer), push, wait for `fuzzer-msvc`, `fuzzer-mingw` and `symex-mingw` (polling at most every 5 minutes), fix any reds, and write the DONE report.

The uncommitted probes in `tests/scratch_s8bi/` are local only and must not be committed. Base probe logs are in `$S/base_*.log`.
