# Job: S8cq -- new slice (batch 9's findings; items 1-3 are false verdicts present at afce42a)

## Setup
- Branch: create `rfc-0005-s8cq` from origin/rfc-0005-batch9 at e497dcf, or from the channel head once I report batch 9 has landed (same sha unless the gate goes red).
- Walker number is assigned at integration; use the next free one above 247 locally, and update the CR2 pin to match.
- Read WORKER-BRIEF.md and WORKER-LOCAL.md first. `tests/tsymex_rfc0005_b9_integration.nim` holds the nearby shapes already fixed in batch 9 (`closureTakesView`, `byValueTouch`, `holdsCompoundLeaf`); start from those.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cq"
title = "Batch 9's findings: by-value sharing on direct calls, direct var-returning actuals, a call evaluated twice under inc and swap, and the declines beside them"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first, against native execution)
1. **SOUNDNESS: direct-call by-value sharing.** Each gives a false sxUnsat on `_live` and a false sxSat on `_dead`:
   - `gWrite(gs)`, where the callee writes the global it also received by value;
   - a nested closure `inner(s)` writing captured `s`;
   - `outerR(gs)`, where a nested call writes `gs`.
   Batch 9's fix covers these shapes only through a proc value. Nim passes a large by-value argument by reference, so the callee can see the write, and whether it does depends on the type. Pin native behaviour across small and large types, on c and cpp, then model what is stable and decline what is not.
2. **SOUNDNESS: direct var-returning actual.** `rab(t["a"], t, "a")` gives the same false pair. Batch 9 fixed it at one call form (around `dsl_parser.nim:7746`). Find every form that reaches the same state.
3. **SOUNDNESS: a call evaluated twice.** `inc(getR()[])` and `swap(getR()[], x)`: `pureLvalueTarget` accepts any deref (`dsl_parser.nim:15700`), so the call runs twice in the model and once natively. `ir_live` and `sr_live` give false sxUnsat; `ir_dead` and `sr_dead` give false sxSat. Fix `pureLvalueTarget` so that an lvalue containing a call cannot be duplicated, then audit every other caller of that predicate and every other arm that lowers one lvalue twice, including `dec`, `+=` forms, `add`, `setLen` and `del`.
4. **Precision.** Model each, with native pins, after item 3 makes the evaluation order right:
   - `inc(gs[nextI()])`, `inc(getV())`, `swap(gs[nextI()], x)`;
   - a read-only by-value global through a proc value (`pr`);
   - `addr` of a global in a walked callee, which halts the path (`wp_dead`, `heUnsafeCast`);
   - `unsafeAddr` of a by-value array formal in a walked callee.

## Verification
- Suites: yours, b9_integration, b9_calldepth, s8ca_* (all), s8cc_remainder, s8by_remainder, s8bs_* (all), s8bl_* (all), s8be_remainder, s8br_remainder, n27, n49, s5_str, emit_roundtrip, CR2.
- Run on Z3 5.1, 4.13.4 and cpp, then the whole tree on Linux once before DONE. All three Windows legs green.
- Report DONE to `worker-reports/s8cq.md`, with per-file Windows times.
- Report anything that also affects main at 6cbfe8f, using a native-checked probe, so it can be sorted for the release.
