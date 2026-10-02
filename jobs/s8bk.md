# Job: S8bk -- new slice (batch-3 integrator's finding). Run it after the batch-3 gate finishes.

**Base.** Branch `rfc-0005-s8bk`, created from origin/rfc-0005-batch3 (d42204d, walker 209). Provisional walker: **212** (S8bi holds 210, S8bj 211).

**RFC row.** Add it before the S11 row in the first commit:
```
[[slice]]
id = "S8bk"
title = "Address-of-argument timing: var/by-ref actuals whose base ref is rebound by a later argument's call"
state = "pending"
```
Flip it to `done` at the end.

## Finding (SOUNDNESS, not yet confirmed in symex)
`orderOperands` handles by-reference and `var` actuals in place. A later argument's call can rebind the base ref, as in `touch(gP.x, moveP())` where `moveP` reassigns the global `gP`. In that case the walker may read the NEW ref. Nim takes the address before the later call runs. A native probe printed `old.x=0 gP.x=5` on both c and cpp, so the write lands in the OLD object.

## Scope (do all of it; defer nothing)
1. **Confirm the bug.** Write a symex target with a dead label that Nim can never reach, plus a reachable twin, and confirm the verdict is wrong. Then pin it RED.
2. **Fix it.** At each argument's evaluation point, snapshot the address an lvalue actual names: the root ref value, plus the path and index values. Bind the callee's `var` or by-reference formal to that snapshot, not to a re-read after later arguments have run.
   - This applies to S8ba's by-reference specialisation, S8bf's peers, `addr` actuals and copy-in/copy-out.
   - Copy-out must write to the snapshot address.
3. **Audit and pin these variants:**
   - an index variable modified by a later argument (`touch(a[i], incI())`);
   - a field-of-field chain rebound partway;
   - a `var` parameter that is forwarded on;
   - an `addr x` actual next to a call that reassigns `x`'s containing ref;
   - the same patterns through a proc variable, if S8bh's indirect-call copy-out is present. Its branch is rfc-0005-s8bh. If it is not on your base, note it in the report.

## Tests and verification
- **Test file:** `tests/tsymex_rfc0005_s8bk_argtiming.nim`, registered in nelli.nimble, under 60 s per backend.
- **Suites to run:** your suite plus s8bf_alias, s8bd, s8ba, s8ax, s8au, s8an, s8ac, s8i_models, s8_scope, CR2, every 163rev suite, and the closure and heap suites.
- **Z3 versions:** run them on both 5.1 and 4.13.4.
- **cpp:** run your own suite once in cpp.
- **Push and Windows:** push `rfc-0005-s8bk`. The coordinator watches the Windows legs if `gh` is not authenticated here.

## Report
Write `worker-reports/s8bk.md` in the DONE format from WORKER-BRIEF.

## REVISION 1 (coordinator, after the S8bk BLOCKER at worker-sls2 11cd931). This supersedes the Finding and Scope above.

The worker's evidence is accepted. Nim takes a var/addr actual's address AFTER the later arguments are evaluated (`T1_ = moveP(); touch(&(*gP).x, T1_);`). The job's "snapshot early" fix was backwards. Implement the agent's corrected design:

1. **Pin the real bug RED** (false sxSat at the base). The value is read early but written back to the late address in:
   - copy-in/copy-out;
   - the S8an addr cell;
   - the S8bd by-ref element base (`gA[gi].x`), which evaluates the index early.
2. **Fixed var/addr operands become late reads**, like S8ax's lazy operands. Both the address and the copied-in value are taken at the call, after every later argument. Copy-out writes back through that same late address.
3. **Address checks stay where Nim does them.**
   - The bound check, nil check, etc. stay at the argument's own position, using the values seen there.
   - When a later argument's call changes what that check read (the `touch(a[gi], incI())` case), Nim accesses through an index it never checked. That is UB. Decline it with `feEvalOrderUnmodelled` and name the reason; never model it as a defined access. Reuse S8ax's snapshot to detect the change.
4. **A call used as the base** (`getB().x`) stays eager and is evaluated exactly once.
5. **The by-ref symbol base (`gP`) is already right.** Pin it so it stays that way.
6. **Proc-variable variants.** S8bh (indirect-call copy-out) is not on this base. Implement and pin the direct-call forms only. The coordinator is adding the proc-variable forms to S8bh's integration.
7. **Pin the native semantics from your probes.** `old.x=10 gP.x=105` is a satisfiable witness that replays roConfirmed. Pin it alongside the dead twin.

Everything else is as above: walker 212, the test file, the verification suites on both Z3 versions, cpp once, a push, then the DONE report.
