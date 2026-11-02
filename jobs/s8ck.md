# Job: S8ck -- new slice, cross-repo (S8ce's remainder; PRIORITY for item 1)

Use opus. **Item 1 runs ahead of the queue**, because S8ce changed every nim-z3 hook and nim-z3 main will not be fast-forwarded until item 1 is clean. Report item 1 to the coordinator as soon as it has a result, before finishing the rest.

## Setup
- nim-z3: create branch `rfc-0005-s8ck` from origin/rfc-0005-s8ce at cc5ffc9. Pushing that branch is authorised. Never push nim-z3 main.
- nelli: create `rfc-0005-s8ck` from origin/rfc-0005-soundness-channels at 136ad60, then merge origin/rfc-0005-s8bx at de6c67f and origin/rfc-0005-s8ce at 62bed1c. If batch 8 has landed by then, base on its head and merge only S8ce; the coordinator will say. If nim-z3 changes, bump the lock as S8ce did and report the new sha and identity.
- Walker number is assigned at integration; use the next free one above 241 locally, and update the CR2 pin to match. If no walker semantics change, leave it alone and say so.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md and worker-reports/s8ce.md first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8ck"
title = "S8ce's remainder: nim-z3's leak gate and examples on the raise-free hooks, the leaks it reports, Z3Ast's unused hooks, nim-z3's suite on Z3 5.1, what the raise-free hooks make redundant"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first where it is a defect)
1. **Run nim-z3's valgrind leak gate and `tests/run.sh examples` at cc5ffc9.** Neither ran. Build a throwaway image or container layer with valgrind through podman; do not change the shared image. Compare against ae509f0, so that existing leaks are told apart from new ones. A double free, use-after-free or invalid read at cc5ffc9 is a soundness-grade defect: fix it on this branch and say so at the top of your message.
2. **The leaks S8ce reported.** `Z3FuncDeclOwn`, `Z3FuncInterpOwn` and `Z3RcfNum` hooks never release `ctx`. Fix them, under `-d:z3CtxDestroyCount` or the leak gate.
3. **`Z3Ast[S: static]`'s custom hooks are not used for `Z3Int` / `Z3Bool`.** S8ce inferred this from the generated C: those values get a field-wise destroy and never dec_ref. Confirm it by observation. Make the hooks apply if that is achievable, and measure the effect on memory and wall time on r4_strip and s8bb_constructs. If applying them makes either materially worse, report the numbers before landing that part.
4. **nim-z3's suite on Z3 5.1.**
   - `tregex_index` hangs on 5.1 at both ae509f0 and cc5ffc9, and passes 37/37 in 2 s on 4.13.4. Find out why. Say whether nelli's walker can reach the same hang, and if it can, pin nelli's bound against it.
   - `tffi`, `tversion` and `tmultiversion` assert a 4.x runtime. Make them correct on both versions.
5. **The `injectShapeFault` comment** in runtime.nim overstates what it shows. Correct it to what S8ce's report says.
6. **What the raise-free hooks make redundant.**
   - ADR-0023's "a lowering-time degrade must never raise" rule and its in-band sinks: keep or simplify, with the reasoning written down. If they still earn their place, say why, and leave the code alone.
   - S8m's `z3ApiErrorCount` fallback, which also counts API errors caught inside the walk. Establish whether that over-count can change a verdict. Fix it if it can.
7. **`tsymex_rfc0005_s8s_precision`'s run wall** rose from 13.2 s to 19.1 s on Windows at S8ce. Trace it. Fix it if the hooks caused it.

## Verification
- nim-z3: full suite on Z3 5.1 and 4.13.4, c and cpp; the leak gate; examples.
- nelli: yours, s8ce (2), s8bx (5), CR2, s8m_exits, r4_strip, s8bb_constructs, s8s_precision. Run on Z3 5.1 and 4.13.4, plus cpp for the new suite. If the hooks change again, also run full `tsymex_*` on c on both Z3 versions.
- All three Windows legs green.
- Report DONE to `worker-reports/s8ck.md`, with per-file Windows times.

## Added after item 1 (worker-reports/s8ck-item1.md)
Item 1 is closed: cc5ffc9 is accepted, and the coordinator read all 17 changed src files and found the refcount conditions preserved. nim-z3 main fast-forwards to cc5ffc9, so everything here stacks on it as later nim-z3 commits.

8. **examples/properties.nim:30** uses `.toInt` on a `Z3Int`, and does not compile. Commit the tested `toInt64` fix. CI only runs `test`, which is how this went unnoticed: add the examples to nim-z3's CI, on c and cpp.
9. **The leak gate cannot fail on an invalid access.** It uses `--error-exitcode=0` and only greps "definitely lost: 0 bytes". Make invalid reads, invalid writes and invalid frees fail it. Add a narrow suppression for the spacer read below, naming the defect. Then show the gate going RED on a planted bad dec_ref.
10. **The Z3 invalid read in spacer::pob_queue::reset().** It is accepted as an upstream Z3 defect; nelli does not reach fixedpoint. Record it in nim-z3's docs, and reduce it to the smallest input you can, with the Z3 versions, for an upstream report. Do not file it.
11. **Generated seq and ref hooks on the raise path.** The hook discipline covers declared hooks, but `seq[Z3Bool]`-style generated hooks are not `quirky`. Pin that a seq of several hook-owning values, destroyed with an exception in flight, releases every element. Fix it if it does not.
12. **Unfreed contexts.** Item 2's fix must separate real leaks from live globals, under `-d:z3CtxDestroyCount`, including `trcf`'s 26 `Z3ContextOwn` blocks and about 430 MB possibly lost.
