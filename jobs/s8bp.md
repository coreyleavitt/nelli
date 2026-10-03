# Job: S8bp -- new slice (S8bm's remainder; all PRECISION)

**Setup:**
- Branch: create `rfc-0005-s8bp` from origin/rfc-0005-s8bm at 14d7e81 (based on 621af8f, walker 214).
- Provisional walker: **219**.
- Read WORKER-BRIEF.md and the "As landed (S8bm)" notes first.

**RFC row:** add it before the S11 row in your first commit, and flip it to `done` at the end:
```
[[slice]]
id = "S8bp"
title = "S8bm's remainder: isolate the post-step-1 solver steps from walk-context state, move per-thread kind probes out of the first walk's context, unbounded endsWith/contains regex query on Z3 4.13.4"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)

1. **Isolate the remaining steps from walk state.**
   - Today, steps (2), uncapped (3), and the no-string-leaf `plain` query still search in the walk's shared context, so their cost moves with what the walk did before.
   - Give them the same isolation S8bm gave step 1: a translated context, or another mechanism you can show makes the cost independent of the preceding walk.
   - Keep the spend accounting exact.
   - Prove the result with determinism tests. Use your 30x "unrelated constant" perturbation probe: the same query, with and without preceding unrelated walk state, should cost about the same in each step.
2. **Move the per-thread kind probes out of the first walk's context.**
   - The probes are `seqCapKinds`, `byteDomainKinds`, `intDivDeclKinds`, and `theoryFreeSimple`'s check.
   - Run them in their own context, so the first walk's context matches later walks'.
   - Pin it with a test showing the first and second walk of the same SUT cost the same.
3. **Fix unbounded `s.endsWith(re"b+") and not s.contains(re"b")` on Z3 4.13.4.**
   - It currently returns sxUnknown: 11.2M units in its second query, `beSolverUndef`.
   - Make it decide on both Z3 versions within the default budget, for example through a regex-level simplification or a better encoding. If it is genuinely beyond Z3 4.13.4, say exactly why with evidence.
   - Then drop S8ay's `s.len <= 8` workaround, or add an unbounded twin of that pin.

## Verification
- **Suites:** run yours, s8bm, s8ba, s8ay, s8aw, s8au, s8ag_indexsplit, s8aj, s1c_verdict, s8y_budget_decline, CR2, and every units/rlimit-asserting suite.
- **Z3 versions:** run them on 5.1 and 4.13.4, plus one cpp run.
- **Report:** push, then report DONE to `worker-reports/s8bp.md` with before and after measurements.
